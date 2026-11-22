"""Apply the existing unrestricted-partner certificate engine to the Round 257 parents."""
from pathlib import Path
import json
import sys
HERE=Path(__file__).resolve().parent
PREV=HERE.parent/"255-parity-exchange-arms"
sys.path.insert(0,str(PREV))
import partners255 as engine


def main():
    two=json.loads((HERE/"two-exchange-comparison/shell-distant.json").read_bytes())
    three=json.loads((HERE/"shell-distant.json").read_bytes())
    old=json.loads((PREV/"summary.json").read_bytes())
    focus=json.loads((PREV/"focus-closure.json").read_bytes())["paths"]
    shapes=two["shapes"]|three["shapes"]
    escaped=sorted(shapes.keys()-focus.keys())
    open_focus=set(old["open_focus_shapes"])
    target=escaped+sorted(two["shapes"].keys()&open_focus)+sorted(three["shapes"].keys()&open_focus)
    if len(escaped)!=2 or len(target)!=25: raise ValueError("Unexpected parent coverage")
    arms=HERE/"partner-input.json"
    data=dict(shapes=shapes,outside_previous=target)
    if arms.exists() and json.loads(arms.read_bytes())!=data: raise ValueError("Inputs changed")
    if not arms.exists():
        arms.write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    engine.HERE=HERE
    engine.ARMS=arms
    engine.LEDGER=HERE/"partner-caps.json"
    engine.main()

if __name__=="__main__": main()
