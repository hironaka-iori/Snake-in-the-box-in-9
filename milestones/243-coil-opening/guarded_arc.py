"""Compile/save a paper or run a bounded search with the project's memory gates."""
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "241-exact-count-distance"))
from compile_receipt import compile_one, memory_limit
sys.path.insert(0, str(HERE.parent / "242-seed-trade-construction"))
from guarded import wait_for_gate
import compile_receipt

if __name__ == "__main__":
    if sys.argv[1] in {"coil-exchanges", "census191"}:
        limit = memory_limit(256)
        name = sys.argv[1]
        log = HERE / (name + ".log")
        source = "coil_exchanges.py" if name == "coil-exchanges" else "census191.py"
        receipt = wait_for_gate([sys.executable, "-B", str(HERE / source)],
                                HERE, log, 360)
        receipt["private_limit"] = limit
        print(log.read_text(), end="")
    elif sys.argv[1] == "sat":
        limit = memory_limit(256)
        length, seconds = int(sys.argv[2]), float(sys.argv[3])
        name = f"sat-{length}-{seconds:g}"
        log = HERE / (name + ".log")
        receipt = wait_for_gate([sys.executable, "-B", str(HERE / "arc_sat.py"), *sys.argv[2:]],
                      HERE, log, 360)
        receipt["private_limit"] = limit
        print(log.read_text(), end="")
    elif len(sys.argv) == 2:
        name = sys.argv[1]
        compile_receipt.run = wait_for_gate
        receipt = compile_one(name)
    else:
        length, budget = map(int, sys.argv[1:])
        limit = memory_limit(256)
        name = f"arc-{length}-{budget}"
        log = HERE / (name + ".log")
        receipt = wait_for_gate([sys.executable, "-B", str(HERE / "open_coil.py"), "--spine", str(length),
                       "--budget", str(budget)], HERE, log, 240)
        receipt["private_limit"] = limit
        print(log.read_text(), end="")
    (HERE / (name + "-receipt.json")).write_text(json.dumps(receipt, indent=2) + "\n",
                                                  encoding="utf-8", newline="\n")
