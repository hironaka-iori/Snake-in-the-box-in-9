"""Reconcile flex-search results by original base walk and alternating offset."""
import json
from collections import Counter
from pathlib import Path

sources = ["q9_flexible_corners_full_192.jsonl", "q9_flexible_endpoint_relative_192.jsonl"]
def read(path):
    with Path(path).open() as stream:
        yield from map(json.loads, stream)

def verify(vertices, target):
    indices = {x:i for i,x in enumerate(vertices)}
    assert len(indices) == len(vertices) >= target+1
    assert min(indices) >= 0 and max(indices) < 512
    for x,i in indices.items():
        adjacent = {indices[x ^ (1<<d)] for d in range(9) if (x ^ (1<<d)) in indices}
        assert adjacent == ({i-1,i+1} & set(range(len(vertices))))

def main():
    rows = {src:{} for src in sources}
    witnesses = []
    for src in sources:
        for s,key,offset,count,w in read(src):
            assert (key,offset) not in rows[src]
            rows[src][(key,offset)] = s
            if w:
                verify(w,192)
                witnesses.append(w)
    initial = {src:dict(Counter(r.values())) for src,r in rows.items()}
    retries = set()
    for s,key,offset,w,src in read("q9_flexible_reverse_relative_192.jsonl"):
        assert (src,key,offset) not in retries
        assert rows[src][(key,offset)] == "UNKNOWN"
        retries.add((src,key,offset))
        rows[src][(key,offset)] = s
        if w:
            verify(w,192)
            witnesses.append(w)
    for f in ("q9_flexible_corners_control.jsonl","q9_flexible_all_neighbors_control.jsonl","q9_adder_control.jsonl"):
        c=[r[-1] for r in read(f) if r[0]=="FOUND"]
        assert c
        for w in c: verify(w,191)
    assert witnesses or len(retries) == sum(c.get("UNKNOWN",0) for c in initial.values())
    report = {"target_edges":192,"original":initial,"after_retry":{src:dict(Counter(r.values())) for src,r in rows.items()},
              "three_axis_retry":dict(Counter(r[0] for r in read("q9_adder_192.jsonl"))),
              "unresolved":{src:[list(key) for key,s in r.items() if s=="UNKNOWN"] for src,r in rows.items()},
              "witnesses":witnesses}
    print(json.dumps(report,indent=2))

if __name__ == "__main__":
    main()
