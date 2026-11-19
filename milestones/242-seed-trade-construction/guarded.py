"""Run one mathematical calculation or typesetter under the Round 241 limits."""
from hashlib import sha256
from pathlib import Path
import json
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "241-exact-count-distance"))
import compile_receipt
from compile_receipt import compile_one, memory_limit, run, snapshot


def wait_for_gate(command, cwd, log, deadline):
    until = time.monotonic() + 180
    while True:
        state = snapshot()
        if not state["errors"] and not state["processes"] and state["free_bytes"] >= 1024**3:
            return run(command, cwd, log, deadline)
        if time.monotonic() >= until:
            raise RuntimeError(("Startup resource gate", state))
        time.sleep(1)


if __name__ == "__main__":
    name = sys.argv[1]
    if name in {"snake9_frontier_explanation", "snake9_research"}:
        compile_receipt.run = wait_for_gate
        receipt = compile_one(name)
    else:
        limit = memory_limit(256)
        source = HERE / (name + ".py")
        log = HERE / (name + ".log")
        receipt = run([sys.executable, "-B", str(source)], HERE, log, 600)
        receipt.update(private_limit=limit, source_sha256=sha256(source.read_bytes()).hexdigest())
        print(log.read_text(encoding="utf-8"), end="")
    (HERE / (name + "-receipt.json")).write_text(json.dumps(receipt, indent=2) + "\n",
                                                 encoding="utf-8", newline="\n")
