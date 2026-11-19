"""Rebuild the frozen joining module and compile the rooted-prefix deduction."""
from datetime import datetime, timezone
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import os
import re
import shutil
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "242-seed-trade-construction"))
from guarded import memory_limit, wait_for_gate
from compile_receipt import PREVIOUS, digest


def main():
    runtime = PREVIOUS / "data" / "EightCubeObstruction240-execution.json"
    compiler = Path(json.loads(runtime.read_bytes())["lean_bin"]) / "lean.exe"
    base = HERE.parent / "188-dimensional-constructions" / "lean" / "LayerJoining.lean"
    program = HERE / "Prefix248.lean"
    names = {base: ["join", "compatibility_necessary", "lengths_for_196", "lengths_for_197",
                    "single_crossing_upper"],
             program: ["takePrefix", "rooted_prefix", "compatible_prefix", "exact_splits", "trim_to_192"]}
    hard_limit = memory_limit(256)
    results = []
    with TemporaryDirectory(prefix="snake-prefix248-") as temporary:
        build = Path(temporary)
        # The only project dependency visible to the second module is the
        # object built from the frozen source by the preceding invocation.
        os.environ["LEAN_PATH"] = str(build)
        for source, declarations in names.items():
            staged = build / source.name
            shutil.copyfile(source, staged)
            source_hash = digest(source)
            if digest(staged) != source_hash:
                raise ValueError("Staged source differs")
            obj = source.stem + ".olean"
            args = ["-j", "1", "-s", "8192", "-o", obj, staged.name]
            log = build / (source.stem + ".log")
            run = wait_for_gate([str(compiler), *args], build, log, 60)
            out = log.read_text(encoding="utf-8")
            reports = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", out)
            expected = {source.stem + "." + name for name in declarations}
            if ({name for name, _ in reports} != expected or len(reports) != len(expected)
                    or any(term in out for term in ("error:", "sorryAx", "warning:"))):
                raise ValueError((source.name, out))
            for _, axioms in reports:
                if not set(re.findall(r"[\w.]+", axioms)) <= {"propext", "Quot.sound", "Classical.choice"}:
                    raise ValueError((source.name, axioms))
            results.append(dict(module=source.stem, source_sha256=source_hash, object_sha256=digest(build/obj),
                                arguments=args, run=run, compiler_output=out))
    receipt = dict(status="pass", compiler=str(compiler), compiler_sha256=digest(compiler), thread_limit=1,
                   deadline_seconds_per_module=60, private_memory_limit=hard_limit, modules=results,
                   finished_utc=datetime.now(timezone.utc).isoformat())
    (HERE / "Prefix248-compile.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("Compiled", ", ".join(r["module"] for r in results), "and checked all named axiom reports")


if __name__ == "__main__":
    main()
