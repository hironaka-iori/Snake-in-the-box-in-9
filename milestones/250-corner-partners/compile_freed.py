"""Compile the two prefix implications in one resource-limited Lean invocation."""
import json
from pathlib import Path
import re
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "242-seed-trade-construction"))
from guarded import wait_for_gate, memory_limit, compile_receipt


def main():
    previous = HERE.parent / "249-long-parent-joins" / "Hinge249-compile.json"
    runtime = json.loads(previous.read_bytes())
    lean = Path(runtime["compiler"])
    digest = compile_receipt.digest
    if digest(lean) != runtime["compiler_sha256"]:
        raise ValueError("Previous Lean runtime differs")
    source = HERE / "FreedSite250.lean"
    limit = memory_limit(256)
    with TemporaryDirectory(prefix="snake-freed250-") as temporary:
        folder = Path(temporary)
        obj = folder / "FreedSite250.olean"
        log = folder / "compile.log"
        args = ["-j", "1", "-s", "8192", "-o", str(obj), source.name]
        execution = wait_for_gate([str(lean), *args], HERE, log, 60)
        out = log.read_text(encoding="utf-8")
        reports = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", out)
        if ({name for name, _ in reports} != {"FreedSite250.forced_hit", "FreedSite250.forced_internal_hit"}
                or len(reports) != 2 or any(s in out for s in ("warning:", "error:", "sorryAx"))):
            raise ValueError(out)
        for _, axioms in reports:
            if not set(re.findall(r"[\w.]+", axioms)) <= {"propext", "Quot.sound", "Classical.choice"}:
                raise ValueError(axioms)
        result = dict(status="pass", compiler=str(lean), compiler_sha256=digest(lean),
                      source_sha256=digest(source), object_sha256=digest(obj), arguments=args,
                      private_memory_limit=limit, thread_limit=1, deadline_seconds=60,
                      execution=execution, compiler_output=out)
    (HERE / "FreedSite250-compile.json").write_text(json.dumps(result, indent=2)+"\n",
                                                    encoding="utf-8", newline="\n")
    print(out)


if __name__ == "__main__":
    main()
