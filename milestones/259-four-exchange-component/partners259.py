"""Check unrestricted opposite arms for the five additional shapes reached in Round 259."""
from hashlib import sha256
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
sys.path.insert(0, str(MS / "255-parity-exchange-arms"))
import partners255 as engine
from enumerate_arms import word

if __name__ == "__main__":
    prior = json.loads((MS/"258-four-exchange-parents/new-arms.json").read_bytes())["shapes"]
    shapes = {}
    for source in sorted(HERE.glob("shell-*-0.json")):
        path = json.loads(source.read_bytes())["reference"]
        key = sha256(word(path)).hexdigest()
        if key not in prior: shapes[key] = path
    engine.HERE = HERE
    engine.ARMS = HERE / "new-arms.json"
    engine.LEDGER = HERE / "partner-caps.json"
    data = dict(shapes=shapes, outside_previous=sorted(shapes))
    if engine.ARMS.exists() and json.loads(engine.ARMS.read_bytes()) != data:
        raise ValueError("Rooted input changed")
    if not engine.ARMS.exists():
        engine.ARMS.write_text(json.dumps(data)+"\n", encoding="utf-8", newline="\n")
    engine.main()
