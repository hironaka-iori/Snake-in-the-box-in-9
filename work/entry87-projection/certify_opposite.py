"""Certify that all rooted free last layers left by the direct opposite-anchor optimization are already optimal."""
import json
from pathlib import Path
from free_last_drat import decide
from solve import save


if __name__=="__main__":
    data=json.loads(Path("opposite-anchors-4000000-20.0.json").read_text());rows=[]
    for r in data["rows"]:
        if r["middle"]["complete"] and r["last"]["complete"]:continue
        assert r["middle"]["complete"] and r["last"]["best"]==48
        A=set(r["left"]);C=r["third"];root=C[-1];free=set(range(128))-(A|set(C))
        domain={v^root for v in free|{root}};tag=f"opposite-{r['index']}-{r['orientation']}"
        ans=decide(domain,49,400000,tag,Path("drat-check.exe").resolve())
        rows.append(dict(source=r["index"],orientation=r["orientation"],domain=sorted(domain),**ans))
    assert len(rows)==3 and all(r["status"]=="UNSAT" for r in rows)
    save(Path("opposite-anchors-last-checked.json"),rows)
    print("All 30 oriented pairs have exact maximum 190 edges.",flush=True)
