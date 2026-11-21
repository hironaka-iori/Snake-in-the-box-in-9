"""Run one research calculation or manuscript build with the saved resource limits."""
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent/"242-seed-trade-construction"))
from guarded import wait_for_gate, memory_limit, compile_one, compile_receipt


if __name__ == "__main__":
    name, *arguments = sys.argv[1:]
    if name in {"snake9_research","snake9_frontier_explanation"}:
        compile_receipt.run = wait_for_gate
        receipt = compile_one(name)
        (HERE/(name+"-receipt.json")).write_text(json.dumps(receipt,indent=2)+"\n",encoding="utf-8",newline="\n")
    else:
        memory_limit(256)
        folder=HERE/"runs"
        folder.mkdir(exist_ok=True)
        stamp=datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
        stem=folder/(name+"-"+stamp)
        log=stem.with_suffix(".log")
        receipt=dict(program=name,arguments=arguments,source_sha256=compile_receipt.digest(HERE/(name+".py")))
        try:
            receipt.update(wait_for_gate([sys.executable,"-B",str(HERE/(name+".py")),*arguments],HERE,log,420))
        except Exception as error:
            receipt["error"]=str(error)
            raise
        finally:
            stem.with_suffix(".json").write_text(json.dumps(receipt,indent=2)+"\n",encoding="utf-8",newline="\n")
        print(log.read_text(encoding="utf-8"))
