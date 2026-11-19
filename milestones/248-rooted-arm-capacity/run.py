from pathlib import Path
import json
import sys
import time

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
        history=HERE/(name+"-interruptions.json")
        for attempt in range(5):
            try:
                record=wait_for_gate([sys.executable,"-B",str(HERE/(name+".py")),*sys.argv[2:]],HERE,log,420)
                break
            except RuntimeError as error:
                message=error.args[0]
                if not isinstance(message,tuple) or message[0] not in ("Startup resource gate","Runtime resource gate"):
                    raise
                entries=json.loads(history.read_bytes()) if history.exists() else []
                entries.append(dict(utc=time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime()),reason=message))
                history.write_text(json.dumps(entries,indent=2)+"\n",encoding="utf-8",newline="\n")
                if attempt==4:
                    raise
                time.sleep(2)
        record["private_limit"]=limit
        print(log.read_text(),end="")
    (HERE/(name+"-receipt.json")).write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8",newline="\n")
