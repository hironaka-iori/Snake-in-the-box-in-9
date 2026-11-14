"""Reproduce the 250,000-conflict experiment on the five saturated models."""
import json
from pathlib import Path
from time import monotonic
from solve import paths,model,save

if __name__=="__main__":
    q=paths()[1]
    records=[]
    for row in sorted(json.loads(Path("saturation.json").read_text()),key=lambda r:r["min_room"]):
        now=monotonic()
        result=model(q,row["bits"],250000,anchors=row["anchors"])
        records.append(dict(bits=row["bits"],seconds=round(monotonic()-now,2),**result))
        save(Path("saturated-search.json"),records)
        if result["status"]=="SAT":
            break
