"""Fresh source-only build and transitive axiom audit of the 245-edge bound.

Requires Python 3.12+, Lean 4.19.0 on PATH, and the pinned mathlib checkout.
No solver results or research-directory compiled objects enter this build.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import tempfile
import threading
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait

PIN = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODULES = [
    "FreshCoordinates", "CubeCoordinateAlgebra", "EndpointGroups",
    "CycleStructure", "SingletonGeometry", "AggregateSingletonBound",
    "ExactWedgeCount", "SingletonAlphaBridge", "NormalizeAdjacentSingletons",
    "AdjacentConfiguration", "AdjacentNeighborhood", "ExceptionRowNeighbors",
    "CoordinateCycle", "AdjacentSingletonExclusion", "UpperBound251",
    "ExtraFreshCoordinates", "TwoMissingPairs", "OneTwoLocal",
    "NormalizeOneTwo", "OneTwoGeometry", "FiniteEndpointCounting",
    "OneTwoNoB", "OneTwoBDCases", "OneTwoBECases",
    "OneTwoDispatch", "Aggregate248", "UpperBound248",
    "EndpointMissingConfig", "SmallPairFamilies", "EndpointGeometry",
    "Aggregate247", "UpperBound247", "EndpointFourWitness",
    "GeneralMissingFamily", "GeneralMissingGeometry", "GeneralOneTwoLocal",
    "GeneralGoodIndex", "ThreeMissingClassification", "GeneralEndpointGroups",
    "OneThreeExclusion", "AdjacentOneThreeExclusion", "OuterMatchingCount",
    "RepeatedOuterConfig", "RepeatedOuterGeometry", "PairFamilySplitting",
    "DistinctOuterConfig", "MiddleMatchingGeometry", "SingleDeltaResources",
    "SingleDeltaBase", "CubeFlipSaturation", "CommonHoleBase",
    "DenseOuterBase", "LocalDenseRows", "DenseRowGroups",
    "CommonHoleIsolated", "DistinctOuterGeometry", "DistinctOuterFamilies",
    "DistinctOuterCounting", "DistinctOuterResources", "RepeatedOuterMatching",
    "SingleDeltaMiddle", "SingleDeltaEndpoints", "SingleDeltaExclusion",
    "DistinctOuterClassification", "DistinctOuterMirror", "CommonHolePairs",
    "StarOuterBase", "EqualOuterPairBase", "OrdinaryOuterBase",
    "OrdinaryOuterCountingDefs", "SharedFiniteClassification", "OrdinaryOuterHoleEndpoints",
    "RowWindowGeometry", "OrdinaryRowGeometry", "OrdinaryPairEndpoints",
    "SharedOuterBase", "OrdinaryIsolatedGeometry", "CommonHoleCounting",
    "CommonHoleEndpointGroups", "OrdinaryIsolatedOneSide", "OrdinaryHoleResources",
    "FourEndpointCounting", "OrdinaryEndpointCount", "SharedFiniteReduction",
    "OrdinaryTwoEndpoints", "StarOuterResidual", "SharedMissingRight",
    "SharedCleanRows", "SharedMissingRightFamilies", "SharedMissingHoleWrappers",
    "SharedOuterSwitch", "OrdinaryEndpointSeparation", "SharedCentralGeometry",
    "SharedCentralMissing", "OrdinaryGoodRowMirror", "SharedCentralMissingExclusion",
    "SharedCoreEndpoints", "SharedCentralDouble", "SharedCentralCSelected",
    "SharedCentralDoubleExclusion", "OrdinaryPartialRows", "OrdinaryMissingStar",
    "SharedCrossStars", "OrdinaryMissingStarCover", "SharedCrossedStars",
    "SharedCrossMissingStar", "SharedCrossStarExclusion", "SharedSwitchExclusion",
    "SharedOrdinaryFork", "SharedOuterExclusion", "RepeatedThreeTwosExclusion",
    "NormalizeThreeCenters", "NormalizeDistinctThreeTwos", "CommonHoleMiddleRestrictions",
    "CommonHoleStarGroups", "CommonHoleExclusion", "ThreeEndpointCounting",
    "StarOuterCounting", "StarOuterEndpointCount", "StarOuterExclusion",
    "ThreeTwosRemainingOrdinary", "StarLeftGeometry", "MixedOuterBase",
    "EqualOuterPairCounting", "MixedPartnerCounting", "MixedIsolatedGeometry",
    "MixedIsolatedOneSide", "MixedIsolatedEndpoints", "TwoEdgeEndpointDemand",
    "MixedEndpointCounting", "MixedOrdinaryEndpoints", "MixedOuterExclusion",
    "EqualOuterPairEndpoints", "EqualOuterPairForce", "EqualOuterPairIncident",
    "EqualOuterPairStar", "EqualOuterPairResidual", "EqualOuterPairExclusion",
    "ThreeTwosRemainingUnequal", "DisjointOrdinaryPartners", "DisjointOneOrdinaryCount",
    "OrdinaryTwoEdgeDemand", "DisjointOrdinaryDemand", "OrdinaryDisjointExclusion",
    "NormalizeSharedThreeTwos", "AlphaRunPotential", "Aggregate245Conditional",
    "UpperBound245", "Alpha223Potential", "Aggregate244Conditional",
    "WindowPotential242", "WindowPotential241", "AggregateWindowConditional",
    "WindowAutomatonDefs", "WindowAutomatonData", "WindowAutomatonLemmas",
    "WindowAutomatonSequence", "WindowAutomatonBridge", "AggregateDirectionConditional",
    "WindowAutomatonLoop", "CubePermutation",
    # kernel-checked RUP refutations of the two (2,2,3) radius-three window CNFs (bridge step G2)
    "WinCNF", "WinRup", "WinRupCmd", "W223RepInputs", "W223RepS00", "W223RepS01",
    "W223RepS02", "W223RepMain", "W223DisInputs", "W223DisS00", "W223DisS01", "W223DisS02",
    "W223DisS03", "W223DisS04", "W223DisS05", "W223DisS06", "W223DisS07", "W223DisS08",
    "W223DisS09", "W223DisMain", "W223",
    # bridge step G1 and the unconditional 244
    "W223G1Defs", "W223G1Data", "W223G1Sound", "W223G1CheckRep", "W223G1CheckDis", "W223G1Snake",
    "W223G1Inst", "UpperBound244",
]


def chain_modules(chain):
    """Modules of a generated direction-automaton chain.  Suffixes ending in `W` are the SWAR
    kernel chains (all transitions of a shape pair in one packed comparison; `gen_lean_swar.py`),
    the others the one-transition-per-step design (`gen_lean_automaton_k.py`); a `C` in the
    suffix marks a lump cap other than 5 (`WindowAutomatonSym`); the 8-symbol (cap 7) SWAR chains
    check their table layout with delta swaps (`WindowAutomatonTranspose`)."""
    extra = (["WindowAutomatonSwar", "WindowAutomatonCode"] if chain.endswith("W") else []) + \
        (["WindowAutomatonSym"] if "C" in chain else []) + \
        (["WindowAutomatonTranspose"] if chain.endswith("C7W") else [])
    spec = [f"WindowAutomaton{chain}Spec"] if chain.endswith("W") else []
    return extra + [f"WindowAutomaton{chain}Data"] + spec + [f"WindowAutomaton{chain}Shard{i}" for i in range(34)] + [
        f"WindowAutomaton{chain}Table", f"WindowAutomaton{chain}Sequence", f"AggregateDirection{chain}Conditional"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-dir", required=True, type=Path)
    parser.add_argument("--core-targets", nargs="*", default=None,
                        help="build only these core modules (default: the core default targets)")
    parser.add_argument("--k5-chain", choices=["K5R3W", "K5R3"], default="K5R3W",
                        help="which Lean chain proves the conditional 238 (default: the SWAR kernel chain)")
    parser.add_argument("--k6-chain", choices=["K6R3W", "K6R3", "K6R3C7W"], default="K6R3W",
                        help="which Lean chain proves the conditional 235 (default: the SWAR kernel chain)")
    parser.add_argument("--extra-chains", nargs="*", default=[],
                        help="further generated chains to check and audit, e.g. K6R3C7W (the cap-7 233 chain)")
    parser.add_argument("--jobs", type=int, default=1,
                        help="check up to this many independent modules at once (a module starts when every "
                             "module it imports is checked; the shards of a chain are independent)")
    parser.add_argument("--build-dir", type=Path, default=None,
                        help="reuse this build directory: steps whose object is newer than its source and "
                             "whose previous run succeeded are not repeated (for machines that restart)")
    args = parser.parse_args()
    k5, k6 = args.k5_chain, args.k6_chain
    # the five-centre chain goes before the six-centre one, after the shared modules
    modules = list(MODULES)
    for chain in [k5, k6, *args.extra_chains]:
        modules += [m for m in chain_modules(chain) if m not in modules]
    project = Path(__file__).resolve().parent
    # the bounds the chosen chains prove, read from their wrapper theorems' names
    def chain_theorem(chain):
        return re.search(r"theorem (upper_\d+_of_direction_windows" + chain + r")\b",
                         (project / "stronger" / f"AggregateDirection{chain}Conditional.lean").read_text()).group(1)
    k5_theorem, k6_theorem = chain_theorem(k5), chain_theorem(k6)
    extra_theorems = [chain_theorem(c) for c in args.extra_chains]
    repo = project.parent.parent
    mathlib = args.mathlib_dir.resolve()
    lake = shutil.which("lake")
    if lake is None:
        raise SystemExit("Put the Lean 4.19.0 toolchain on PATH first.")
    actual = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=mathlib, text=True
    ).strip()
    if actual != PIN:
        raise SystemExit(f"Expected mathlib {PIN}; found {actual}")
    subprocess.run(
        ["git", "diff", "--exit-code", "HEAD", "--", "*.lean", "lean-toolchain",
         "lake-manifest.json"], cwd=mathlib, check=True,
    )
    version = subprocess.check_output(
        [lake, "env", "lean", "--version"], cwd=mathlib, text=True
    ).strip()
    if "version 4.19.0" not in version:
        raise SystemExit("Expected Lean 4.19.0: " + version)

    build_parent = project / ".verification"
    build_parent.mkdir(exist_ok=True)
    if args.build_dir is not None:
        build = args.build_dir.resolve()
        build.mkdir(parents=True, exist_ok=True)
    else:
        build = Path(tempfile.mkdtemp(prefix="strengthened-", dir=build_parent)).resolve()
    core = build / "core"
    core.mkdir(exist_ok=True)
    logs = build / "logs"
    logs.mkdir(exist_ok=True)
    manifest = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "mathlib_commit": actual, "lean_version": version,
        "build_directory": str(build), "k5_chain": k5, "k6_chain": k6,
        "extra_chains": args.extra_chains, "source_sha256": {},
        "steps": [], "axiom_audits": {}, "status": "running",
    }

    lock = threading.RLock()

    def save():
        with lock:
            (build / "manifest.json").write_text(
                json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
            )

    def copy(source, target):
        source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
        manifest["source_sha256"][source.relative_to(repo).as_posix()] = source_hash
        shutil.copy2(source, target)
        assert hashlib.sha256(target.read_bytes()).hexdigest() == source_hash

    def imported_objects(source):
        """Objects of the modules `source` imports that this build produces (the build directory
        or the core project); mathlib is pinned and not tracked."""
        objects = []
        for name in re.findall(r"^import\s+(\S+)", source.read_text(encoding="utf-8"), re.M):
            rel = name.replace(".", "/") + ".olean"
            for candidate in (build / rel, core / ".lake/build/lib/lean" / rel):
                if candidate.exists():
                    objects.append(candidate)
                    break
        return objects

    def cached(label, source, target):
        # an object is reused only if it is newer than its source AND than every object it
        # imports: a rebuilt dependency (whose definitions may have changed) forces a rebuild,
        # and modules are checked in dependency order, so this propagates transitively
        marker = logs / (label + ".ok")
        return (args.build_dir is not None and marker.exists() and target.exists()
                and target.stat().st_mtime >= source.stat().st_mtime
                and marker.stat().st_mtime >= source.stat().st_mtime
                and all(target.stat().st_mtime >= dep.stat().st_mtime for dep in imported_objects(source)))

    def run(label, command, cwd, env=None):
        print(f"Checking {label} ...", flush=True)
        started = time.monotonic()
        result = subprocess.run(
            command, cwd=cwd, env=env, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace",
        )
        (logs / f"{label}.log").write_text(result.stdout, encoding="utf-8")
        with lock:
            manifest["steps"].append({"label": label, "command": command,
                                       "exit_code": result.returncode,
                                       "seconds": round(time.monotonic() - started, 1)})
            for theorem, raw in re.findall(
                r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout
            ):
                axioms = {item.strip() for item in raw.split(",") if item.strip()}
                manifest["axiom_audits"][theorem] = sorted(axioms)
                if not axioms <= ALLOWED_AXIOMS:
                    save()
                    raise RuntimeError(f"Unexpected axioms for {theorem}: {axioms}")
            save()
        if result.returncode or "declaration uses 'sorry'" in result.stdout:
            print(result.stdout, flush=True)
            raise RuntimeError(f"{label} failed; see {logs / (label + '.log')}")
        (logs / (label + ".ok")).write_text(datetime.now(timezone.utc).isoformat() + "\n")

    try:
        core_source = project.parent / "final_lean"
        for source in [*sorted(core_source.glob("*.lean")),
                       *[core_source / name for name in
                         ("lakefile.toml", "lean-toolchain", "lake-manifest.json")]]:
            copy(source, core / source.name)
        env = os.environ.copy()
        env.pop("LEAN_PATH", None)
        run("core", [lake, "build", *(args.core_targets or [])], core, env)
        copy(project / "SquareIncidence.lean", build / "SquareIncidence.lean")
        for module in modules:
            copy(project / "stronger" / (module + ".lean"), build / (module + ".lean"))
        # The mathlib workspace environment, captured once (`lake env` costs tens of seconds per call).
        lake_env = {}
        for line in subprocess.check_output([lake, "env"], cwd=mathlib, env=env, text=True).splitlines():
            if "=" in line:
                key, value = line.split("=", 1)
                lake_env[key] = value
        lean_bin = lake_env.get("LEAN") or shutil.which("lean")
        env.update(lake_env)
        env["LEAN_PATH"] = os.pathsep.join(
            [path for path in lake_env.get("LEAN_PATH", "").split(os.pathsep) if path]
            + [str(core / ".lake/build/lib/lean"), str(build)])
        order = ["SquareIncidence", *modules]
        # dependencies among the modules of this run, from their import lines
        deps = {m: {name for name in re.findall(r"^import\s+(\S+)",
                                                (build / (m + ".lean")).read_text(encoding="utf-8"), re.M)
                    if name in order} for m in order}

        def check(module):
            # decided when every import is checked, so a rebuilt import makes the object stale
            if cached(module, build / (module + ".lean"), build / (module + ".olean")):
                print(f"Checking {module} ... (object up to date from an earlier run)", flush=True)
                with lock:
                    manifest["steps"].append({"label": module, "cached": True})
                    save()
                return
            run(module, [lean_bin, f"--root={build}", "-o",
                         str(build / (module + ".olean")), str(build / (module + ".lean"))],
                mathlib, env)

        finished, pending, running = set(), list(order), {}
        with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
            while pending or running:
                for module in [m for m in pending if deps[m] <= finished][:max(1, args.jobs) - len(running)]:
                    pending.remove(module)
                    running[pool.submit(check, module)] = module
                if not running:
                    raise RuntimeError(f"unsatisfiable imports among {pending}")
                done, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in done:
                    future.result()            # re-raises a failed check
                    finished.add(running.pop(future))
        audit = build / "FinalAudit.lean"
        audit.write_text(
            "import Aggregate244Conditional\nimport CubePermutation\nimport W223\nimport UpperBound244\nimport AggregateWindowConditional\nimport AggregateDirectionConditional\nimport AggregateDirection" + k5 + "Conditional\nimport AggregateDirection" + k6 + "Conditional\n"
            + "".join(f"import AggregateDirection{c}Conditional\n" for c in args.extra_chains)
            + "import UpperBound245\nimport EndpointFourWitness\nimport AdjacentOneThreeExclusion\nimport OptimalityTarget\n"
            "#print axioms Snake9.upper_244_of_no_two_two_three\n"
            "#print axioms Snake9.upper_242_of_certified_windows\n"
            "#print axioms Snake9.upper_241_of_certified_windows\n"
            "#print axioms Snake9.upper_239_of_direction_windows\n"
            "#print axioms Snake9.WindowAutomaton.step_table\n"
            "#print axioms Snake9." + k5_theorem + "\n"
            "#print axioms Snake9." + k6_theorem + "\n"
            + "".join(f"#print axioms Snake9.{t}\n" for t in extra_theorems) +
            "#print axioms Snake9.lower_bound\n"
            "#print axioms Snake9.noNext_iff_upperBound\n"
            "#print axioms Snake9.adjacent_internal_alpha_one_impossible\n"
            "#print axioms Snake9.upper_bound_251\n"
            "#print axioms Snake9.verified_interval_191_251\n"
            "#print axioms Snake9.CubePerm.exists_normalizing_cubeMap\n"
            "#print axioms Snake9.CubePerm.no223_window_cubeMap\n"
            "#print axioms w223_rep_unsat\n"
            "#print axioms w223_dis_unsat\n"
            "#print axioms W223G1.no_223\n"
            "#print axioms Snake9.upper_bound_244\n"
            "#print axioms Snake9.verified_interval_191_244\n", encoding="utf-8"
        )
        with audit.open("a", encoding="utf-8") as stream:
            stream.write(
                "#print axioms Snake9.adjacent_internal_one_two_impossible\n"
                "#print axioms Snake9.upper_bound_248\n"
                "#print axioms Snake9.verified_interval_191_248\n"
                "#print axioms Snake9.endpoint_alpha_ge_four\n"
                "#print axioms Snake9.upper_bound_247\n"
                "#print axioms Snake9.verified_interval_191_247\n"
                "#print axioms EndpointFourWitness.endpoint_singleton_count\n"
                "#print axioms Snake9.adjacent_internal_one_three_impossible\n"
                "#print axioms Snake9.alpha_one_internal_neighbor_ge_four\n"
                "#print axioms Snake9.no_three_consecutive_internal_twos\n"
                "#print axioms Snake9.upper_bound_245\n"
                "#print axioms Snake9.verified_interval_191_245\n"
            )
        run("FinalAudit", [lean_bin, f"--root={build}", str(audit)], mathlib, env)
        expected = {"Snake9.upper_244_of_no_two_two_three",
                    "Snake9.upper_242_of_certified_windows", "Snake9.upper_241_of_certified_windows",
                    "Snake9.upper_239_of_direction_windows", "Snake9.WindowAutomaton.step_table",
                    "Snake9." + k5_theorem, "Snake9." + k6_theorem, "Snake9.lower_bound", "Snake9.noNext_iff_upperBound",
                    "Snake9.adjacent_internal_alpha_one_impossible",
                    "Snake9.upper_bound_251", "Snake9.verified_interval_191_251",
                    "Snake9.adjacent_internal_one_two_impossible",
                    "Snake9.upper_bound_248", "Snake9.verified_interval_191_248",
                    "Snake9.endpoint_alpha_ge_four", "Snake9.upper_bound_247",
                    "Snake9.verified_interval_191_247", "EndpointFourWitness.endpoint_singleton_count",
                    "Snake9.adjacent_internal_one_three_impossible", "Snake9.alpha_one_internal_neighbor_ge_four",
                    "Snake9.no_three_consecutive_internal_twos", "Snake9.upper_bound_245",
                    "Snake9.verified_interval_191_245"}
        expected |= {"Snake9." + t for t in extra_theorems}
        missing = expected - manifest["axiom_audits"].keys()
        if missing:
            raise RuntimeError(f"Missing final theorem audits: {missing}")
        manifest["status"] = "success"
        manifest["completed_utc"] = datetime.now(timezone.utc).isoformat()
        print("Verified: 191 <= a(9) <= 244 edges (verified_interval_191_244). Exact optimum unresolved.", flush=True)
        print(f"Source hashes, commands, and transitive axiom audits: {build / 'manifest.json'}")
    except BaseException as exc:
        manifest["status"] = "failed"
        manifest["error"] = str(exc)
        raise
    finally:
        save()


if __name__ == "__main__":
    main()
