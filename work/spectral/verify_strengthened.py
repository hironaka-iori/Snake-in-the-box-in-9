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
    "WindowAutomatonLoop", "WindowAutomatonK5R3Data", "WindowAutomatonK5R3Shard0", "WindowAutomatonK5R3Shard1", "WindowAutomatonK5R3Shard2", "WindowAutomatonK5R3Shard3", "WindowAutomatonK5R3Shard4", "WindowAutomatonK5R3Shard5", "WindowAutomatonK5R3Shard6", "WindowAutomatonK5R3Shard7", "WindowAutomatonK5R3Shard8", "WindowAutomatonK5R3Shard9", "WindowAutomatonK5R3Shard10", "WindowAutomatonK5R3Shard11", "WindowAutomatonK5R3Shard12", "WindowAutomatonK5R3Shard13", "WindowAutomatonK5R3Shard14", "WindowAutomatonK5R3Shard15", "WindowAutomatonK5R3Shard16", "WindowAutomatonK5R3Shard17", "WindowAutomatonK5R3Shard18", "WindowAutomatonK5R3Shard19", "WindowAutomatonK5R3Shard20", "WindowAutomatonK5R3Shard21", "WindowAutomatonK5R3Shard22", "WindowAutomatonK5R3Shard23", "WindowAutomatonK5R3Shard24", "WindowAutomatonK5R3Shard25", "WindowAutomatonK5R3Shard26", "WindowAutomatonK5R3Shard27", "WindowAutomatonK5R3Shard28", "WindowAutomatonK5R3Shard29", "WindowAutomatonK5R3Shard30", "WindowAutomatonK5R3Shard31", "WindowAutomatonK5R3Shard32", "WindowAutomatonK5R3Shard33",
    "WindowAutomatonK5R3Table", "WindowAutomatonK5R3Sequence", "AggregateDirectionK5R3Conditional",
]


def k6_modules(chain):
    """The k = 6 (235-edge) chain: K6R3W checks the table with the SWAR kernel (36 transitions per
    big-integer step), K6R3 is the earlier one-transition-per-step design; both prove the same bound."""
    extra = ["WindowAutomatonSwar"] if chain == "K6R3W" else []
    return extra + [f"WindowAutomaton{chain}Data"] + [f"WindowAutomaton{chain}Shard{i}" for i in range(34)] + [
        f"WindowAutomaton{chain}Table", f"WindowAutomaton{chain}Sequence", f"AggregateDirection{chain}Conditional"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-dir", required=True, type=Path)
    parser.add_argument("--core-targets", nargs="*", default=None,
                        help="build only these core modules (default: the core default targets)")
    parser.add_argument("--k6-chain", choices=["K6R3W", "K6R3"], default="K6R3W",
                        help="which Lean chain proves the conditional 235 (default: the SWAR kernel chain)")
    parser.add_argument("--build-dir", type=Path, default=None,
                        help="reuse this build directory: steps whose object is newer than its source and "
                             "whose previous run succeeded are not repeated (for machines that restart)")
    args = parser.parse_args()
    modules = MODULES + k6_modules(args.k6_chain)
    k6 = args.k6_chain
    project = Path(__file__).resolve().parent
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
        "build_directory": str(build), "k6_chain": k6, "source_sha256": {},
        "steps": [], "axiom_audits": {}, "status": "running",
    }

    def save():
        (build / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
        )

    def copy(source, target):
        source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
        manifest["source_sha256"][source.relative_to(repo).as_posix()] = source_hash
        shutil.copy2(source, target)
        assert hashlib.sha256(target.read_bytes()).hexdigest() == source_hash

    def cached(label, source, target):
        marker = logs / (label + ".ok")
        return (args.build_dir is not None and marker.exists() and target.exists()
                and target.stat().st_mtime >= source.stat().st_mtime
                and marker.stat().st_mtime >= source.stat().st_mtime)

    def run(label, command, cwd, env=None):
        print(f"Checking {label} ...", flush=True)
        started = time.monotonic()
        result = subprocess.run(
            command, cwd=cwd, env=env, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace",
        )
        (logs / f"{label}.log").write_text(result.stdout, encoding="utf-8")
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
        for module in ["SquareIncidence", *modules]:
            if cached(module, build / (module + ".lean"), build / (module + ".olean")):
                print(f"Checking {module} ... (object up to date from an earlier run)", flush=True)
                manifest["steps"].append({"label": module, "cached": True})
                save()
                continue
            run(module, [lean_bin, f"--root={build}", "-o",
                         str(build / (module + ".olean")), str(build / (module + ".lean"))],
                mathlib, env)
        audit = build / "FinalAudit.lean"
        audit.write_text(
            "import Aggregate244Conditional\nimport AggregateWindowConditional\nimport AggregateDirectionConditional\nimport AggregateDirectionK5R3Conditional\nimport AggregateDirection" + k6 + "Conditional\nimport UpperBound245\nimport EndpointFourWitness\nimport AdjacentOneThreeExclusion\nimport OptimalityTarget\n"
            "#print axioms Snake9.upper_244_of_no_two_two_three\n"
            "#print axioms Snake9.upper_242_of_certified_windows\n"
            "#print axioms Snake9.upper_241_of_certified_windows\n"
            "#print axioms Snake9.upper_239_of_direction_windows\n"
            "#print axioms Snake9.WindowAutomaton.step_table\n"
            "#print axioms Snake9.upper_238_of_direction_windowsK5R3\n"
            "#print axioms Snake9.upper_235_of_direction_windows" + k6 + "\n"
            "#print axioms Snake9.lower_bound\n"
            "#print axioms Snake9.noNext_iff_upperBound\n"
            "#print axioms Snake9.adjacent_internal_alpha_one_impossible\n"
            "#print axioms Snake9.upper_bound_251\n"
            "#print axioms Snake9.verified_interval_191_251\n", encoding="utf-8"
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
                    "Snake9.upper_238_of_direction_windowsK5R3", "Snake9.upper_235_of_direction_windows" + k6, "Snake9.lower_bound", "Snake9.noNext_iff_upperBound",
                    "Snake9.adjacent_internal_alpha_one_impossible",
                    "Snake9.upper_bound_251", "Snake9.verified_interval_191_251",
                    "Snake9.adjacent_internal_one_two_impossible",
                    "Snake9.upper_bound_248", "Snake9.verified_interval_191_248",
                    "Snake9.endpoint_alpha_ge_four", "Snake9.upper_bound_247",
                    "Snake9.verified_interval_191_247", "EndpointFourWitness.endpoint_singleton_count",
                    "Snake9.adjacent_internal_one_three_impossible", "Snake9.alpha_one_internal_neighbor_ge_four",
                    "Snake9.no_three_consecutive_internal_twos", "Snake9.upper_bound_245",
                    "Snake9.verified_interval_191_245"}
        missing = expected - manifest["axiom_audits"].keys()
        if missing:
            raise RuntimeError(f"Missing final theorem audits: {missing}")
        manifest["status"] = "success"
        manifest["completed_utc"] = datetime.now(timezone.utc).isoformat()
        print("Verified: 191 <= a(9) <= 245 edges. Exact optimum unresolved.", flush=True)
        print(f"Source hashes, commands, and transitive axiom audits: {build / 'manifest.json'}")
    except BaseException as exc:
        manifest["status"] = "failed"
        manifest["error"] = str(exc)
        raise
    finally:
        save()


if __name__ == "__main__":
    main()
