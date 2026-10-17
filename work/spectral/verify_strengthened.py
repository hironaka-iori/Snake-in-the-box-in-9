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
    "WindowAutomaton5Data", "WindowAutomaton5Shard0", "WindowAutomaton5Shard1", "WindowAutomaton5Shard2", "WindowAutomaton5Shard3", "WindowAutomaton5Shard4", "WindowAutomaton5Shard5", "WindowAutomaton5Shard6", "WindowAutomaton5Shard7", "WindowAutomaton5Shard8", "WindowAutomaton5Shard9", "WindowAutomaton5Shard10", "WindowAutomaton5Shard11", "WindowAutomaton5Shard12", "WindowAutomaton5Shard13", "WindowAutomaton5Shard14", "WindowAutomaton5Shard15", "WindowAutomaton5Shard16", "WindowAutomaton5Shard17", "WindowAutomaton5Shard18", "WindowAutomaton5Shard19", "WindowAutomaton5Shard20", "WindowAutomaton5Shard21", "WindowAutomaton5Shard22", "WindowAutomaton5Shard23", "WindowAutomaton5Shard24", "WindowAutomaton5Shard25", "WindowAutomaton5Shard26", "WindowAutomaton5Shard27", "WindowAutomaton5Shard28", "WindowAutomaton5Shard29", "WindowAutomaton5Shard30", "WindowAutomaton5Shard31", "WindowAutomaton5Shard32", "WindowAutomaton5Shard33",
    "WindowAutomaton5Table", "WindowAutomaton5Sequence", "AggregateDirection238Conditional",
    "WindowAutomatonLoop", "WindowAutomatonK6R3Data", "WindowAutomatonK6R3Shard0", "WindowAutomatonK6R3Shard1", "WindowAutomatonK6R3Shard2", "WindowAutomatonK6R3Shard3", "WindowAutomatonK6R3Shard4", "WindowAutomatonK6R3Shard5", "WindowAutomatonK6R3Shard6", "WindowAutomatonK6R3Shard7", "WindowAutomatonK6R3Shard8", "WindowAutomatonK6R3Shard9", "WindowAutomatonK6R3Shard10", "WindowAutomatonK6R3Shard11", "WindowAutomatonK6R3Shard12", "WindowAutomatonK6R3Shard13", "WindowAutomatonK6R3Shard14", "WindowAutomatonK6R3Shard15", "WindowAutomatonK6R3Shard16", "WindowAutomatonK6R3Shard17", "WindowAutomatonK6R3Shard18", "WindowAutomatonK6R3Shard19", "WindowAutomatonK6R3Shard20", "WindowAutomatonK6R3Shard21", "WindowAutomatonK6R3Shard22", "WindowAutomatonK6R3Shard23", "WindowAutomatonK6R3Shard24", "WindowAutomatonK6R3Shard25", "WindowAutomatonK6R3Shard26", "WindowAutomatonK6R3Shard27", "WindowAutomatonK6R3Shard28", "WindowAutomatonK6R3Shard29", "WindowAutomatonK6R3Shard30", "WindowAutomatonK6R3Shard31", "WindowAutomatonK6R3Shard32", "WindowAutomatonK6R3Shard33",
    "WindowAutomatonK6R3Table", "WindowAutomatonK6R3Sequence", "AggregateDirectionK6R3Conditional",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-dir", required=True, type=Path)
    parser.add_argument("--core-targets", nargs="*", default=None,
                        help="build only these core modules (default: the core default targets)")
    args = parser.parse_args()
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
    build = Path(tempfile.mkdtemp(prefix="strengthened-", dir=build_parent)).resolve()
    core = build / "core"
    core.mkdir()
    logs = build / "logs"
    logs.mkdir()
    manifest = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "mathlib_commit": actual, "lean_version": version,
        "build_directory": str(build), "source_sha256": {},
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

    def run(label, command, cwd, env=None):
        print(f"Checking {label} ...", flush=True)
        result = subprocess.run(
            command, cwd=cwd, env=env, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace",
        )
        (logs / f"{label}.log").write_text(result.stdout, encoding="utf-8")
        manifest["steps"].append({"label": label, "command": command,
                                   "exit_code": result.returncode})
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
        for module in MODULES:
            copy(project / "stronger" / (module + ".lean"), build / (module + ".lean"))
        env["LEAN_PATH"] = os.pathsep.join([str(core / ".lake/build/lib/lean"), str(build)])
        for module in ["SquareIncidence", *MODULES]:
            run(module, [lake, "env", "lean", f"--root={build}", "-o",
                         str(build / (module + ".olean")), str(build / (module + ".lean"))],
                mathlib, env)
        audit = build / "FinalAudit.lean"
        audit.write_text(
            "import Aggregate244Conditional\nimport AggregateWindowConditional\nimport AggregateDirectionConditional\nimport AggregateDirection238Conditional\nimport AggregateDirectionK6R3Conditional\nimport UpperBound245\nimport EndpointFourWitness\nimport AdjacentOneThreeExclusion\nimport OptimalityTarget\n"
            "#print axioms Snake9.upper_244_of_no_two_two_three\n"
            "#print axioms Snake9.upper_242_of_certified_windows\n"
            "#print axioms Snake9.upper_241_of_certified_windows\n"
            "#print axioms Snake9.upper_239_of_direction_windows\n"
            "#print axioms Snake9.WindowAutomaton.step_table\n"
            "#print axioms Snake9.upper_238_of_direction_windows5\n"
            "#print axioms Snake9.upper_235_of_direction_windowsK6R3\n"
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
        run("FinalAudit", [lake, "env", "lean", f"--root={build}", str(audit)], mathlib, env)
        expected = {"Snake9.upper_244_of_no_two_two_three",
                    "Snake9.upper_242_of_certified_windows", "Snake9.upper_241_of_certified_windows",
                    "Snake9.upper_239_of_direction_windows", "Snake9.WindowAutomaton.step_table",
                    "Snake9.upper_238_of_direction_windows5", "Snake9.upper_235_of_direction_windowsK6R3", "Snake9.lower_bound", "Snake9.noNext_iff_upperBound",
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
