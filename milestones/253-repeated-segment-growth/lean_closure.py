"""Compile the generic closure argument with the archived Lean runtime and limits."""
import json
from pathlib import Path
import re
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "242-seed-trade-construction"))
from guarded import compile_receipt, memory_limit, wait_for_gate


def main():
    prior = HERE.parent / "251-eighty-edge-segments" / "Suffix251-compile.json"
    runtime = json.loads(prior.read_bytes())
    compiler = Path(runtime["compiler"])
    digest = compile_receipt.digest
    if digest(compiler) != runtime["compiler_sha256"]:
        raise ValueError("Compiler differs from archived runtime")
    source = HERE / "SegmentClosure253.lean"
    limit = memory_limit(256)
    with TemporaryDirectory(prefix="snake-closure253-") as temporary:
        folder = Path(temporary)
        obj = folder / "SegmentClosure253.olean"
        log = folder / "compiler.log"
        args = ["-j", "1", "-s", "8192", "-o", str(obj), source.name]
        execution = wait_for_gate([str(compiler), *args], HERE, log, 60)
        output = log.read_text(encoding="utf-8")
        reports = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", output)
        expected = {"SegmentClosure253."+s for s in ("relay_iff_listed", "terminal_iff_listed", "joined_bound")}
        if ({name for name, _ in reports} != expected or len(reports) != len(expected)
                or any(s in output for s in ("warning:", "error:", "sorryAx"))):
            raise ValueError(output)
        for _, axioms in reports:
            if not set(re.findall(r"[\w.]+", axioms)) <= {"propext", "Quot.sound", "Classical.choice"}:
                raise ValueError(axioms)
        receipt = dict(status="pass", compiler=str(compiler), compiler_sha256=digest(compiler),
                       source_sha256=digest(source), object_sha256=digest(obj), arguments=args,
                       thread_limit=1, deadline_seconds=60, private_memory_limit=limit,
                       execution=execution, compiler_output=output)
    (HERE / "SegmentClosure253-compile.json").write_text(json.dumps(receipt, indent=2)+"\n",
                                                         encoding="utf-8", newline="\n")
    print(output)


if __name__ == "__main__":
    main()
