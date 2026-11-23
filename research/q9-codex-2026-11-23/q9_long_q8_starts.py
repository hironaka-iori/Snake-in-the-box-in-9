"""Enumerate all in-layer continuations before the first crossing, from each 96-edge subpath."""
import json,sys
from pathlib import Path

def code(arm):
    labels={}
    return tuple(labels.setdefault(a^b,len(labels)) for a,b in zip(arm,arm[1:]))
def roots(ref, length=96):
    seen={}
    def visit(arm):
        key=code(arm)
        if key in seen:return
        seen[key]=arm
        for d in range(8):
            v=arm[-1]^(1<<d)
            if v not in arm and all((v^u).bit_count()!=1 for u in arm[:-1]):visit(arm+[v])
    for i in range(len(ref)-length):
        a=ref[i:i+length+1]
        visit(a);visit(a[::-1])
    return [arm[::-1] for arm in seen.values()]

if __name__=="__main__":
    ref=json.loads(Path(sys.argv[1]).read_text())["vertex_sequence"]
    for inward in roots(ref):
        remaining=[v for v in range(256) if v not in inward and all((v^x).bit_count()!=1 for x in inward)]
        assert all((x^y).bit_count()>1 for x in remaining for y in remaining if x!=y)
        print(json.dumps(inward))
