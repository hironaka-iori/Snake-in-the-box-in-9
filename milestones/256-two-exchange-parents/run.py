"""Run one milestone computation with the existing project resource guard."""
from pathlib import Path
import json
import sys
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "242-seed-trade-construction"))
from guarded import wait_for_gate, memory_limit, compile_one, compile_receipt

if __name__ == "__main__":
    dest = Path(sys.argv[1]).resolve()
    logdir = dest.parent / "runs"
    logdir.mkdir(exist_ok=True)
    stem = logdir / (dest.stem+"-"+datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ"))
    log = stem.with_suffix(".log")
    memory_limit(256)
    if dest.suffix == ".tex":
        compile_receipt.run = wait_for_gate
        receipt = compile_one(dest.stem)
    else:
        receipt = wait_for_gate([sys.executable,"-B",str(dest),*sys.argv[2:]],dest.parent,log,900)
        receipt.update(script=dest.name,arguments=sys.argv[2:],source_sha256=compile_receipt.digest(dest))
        print(log.read_text(encoding="utf-8"))
    stem.with_suffix(".json").write_text(json.dumps(receipt,indent=2)+"\n",encoding="utf-8",newline="\n")
