from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"242-seed-trade-construction"))
from guarded import wait_for_gate, memory_limit, compile_one, compile_receipt

if __name__=="__main__":
    name=sys.argv[1]
    if name.startswith("snake9_"):
        compile_receipt.run=wait_for_gate
        record=compile_one(name)
    else:
        limit=memory_limit(256)
        log=HERE/(name+".log")
        record=wait_for_gate([sys.executable,"-B",str(HERE/(name+".py"))],HERE,log,360)
        record["private_limit"]=limit
        print(log.read_text(),end="")
    (HERE/(name+"-receipt.json")).write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8",newline="\n")
