"""Use the unrestricted-partner certificate model for arms newly produced in this round."""
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
sys.path.insert(0,str(MS/"255-parity-exchange-arms"))
import partners255 as engine

def main():
    new={}
    old=set(json.loads((MS/"253-repeated-segment-growth/closure.json").read_bytes())["paths"])
    for f,k in [(MS/"254-distant-arm-partners/parity-families.json","shapes"),
                (MS/"255-parity-exchange-arms/focus-closure.json","paths")]:
        old.update(json.loads(f.read_bytes())[k])
    for source in HERE.glob("shell-*.json"):
        for k,p in json.loads(source.read_bytes())["shapes"].items():
            if k not in old: new.setdefault(k,p)
    data=dict(shapes=new,outside_previous=sorted(new))
    arms=HERE/"new-arms.json"
    if arms.exists() and json.loads(arms.read_bytes())!=data: raise ValueError("Inputs changed")
    if not arms.exists(): arms.write_text(json.dumps(data)+"\n",encoding="utf-8",newline="\n")
    engine.HERE=HERE
    engine.ARMS=arms
    engine.LEDGER=HERE/"partner-caps.json"
    engine.main()

if __name__=="__main__": main()
