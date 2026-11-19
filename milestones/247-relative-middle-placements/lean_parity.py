"""Compile the alternating-colour lemma under the existing single-compiler limits."""
from datetime import datetime, timezone
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "242-seed-trade-construction"))
from guarded import memory_limit, wait_for_gate
from compile_receipt import PREVIOUS, digest


def main():
    source = HERE / "ArmParity247.lean"
    runtime = PREVIOUS / "data" / "EightCubeObstruction240-execution.json"
    compiler = Path(json.loads(runtime.read_bytes())["lean_bin"]) / "lean.exe"
    log = HERE / "lean_parity.log"
    hard_limit = memory_limit(256)
    with TemporaryDirectory(prefix="arm-parity-247-") as directory:
        obj = Path(directory) / "ArmParity247.olean"
        args = ["-j", "1", "-s", "8192", "-o", str(obj), source.name]
        run = wait_for_gate([str(compiler), *args], HERE, log, 60)
        output = log.read_text(encoding="utf-8")
        reports = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", output)
        expected = {"ArmParity247." + name for name in ("colour_counts", "colour_quota", "endColour_by_parity")}
        if ({name for name, _ in reports} != expected or len(reports) != len(expected)
                or any(mark in output for mark in ("error:", "warning:", "sorryAx"))):
            raise ValueError(output)
        for _, names in reports:
            if not set(re.findall(r"[\w.]+", names)) <= {"propext", "Quot.sound", "Classical.choice"}:
                raise ValueError(output)
        receipt = dict(status="pass", source_sha256=digest(source), compiler=str(compiler),
                       compiler_sha256=digest(compiler), arguments=args, thread_limit=1, deadline_seconds=60,
                       private_memory_limit=hard_limit, run=run, object_sha256=digest(obj),
                       compiler_output=output, finished_utc=datetime.now(timezone.utc).isoformat())
    (HERE / "ArmParity247-compile.json").write_text(json.dumps(receipt, indent=2) + "\n",
                                                  encoding="utf-8", newline="\n")
    print(output, end="")


if __name__ == "__main__":
    main()
