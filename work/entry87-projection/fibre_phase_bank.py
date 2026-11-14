"""Count every placement on both faces compatible with each source's unordered fibres."""
from collections import Counter
import json
from pathlib import Path
from fibre_laplacian import decide
from bank_pivots import canonical_word
from solve import BANK,BANK_HASH,sha256,save


if __name__=="__main__":
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    data=json.loads(raw);rows=[];hist=Counter();found=set()
    for i,r in enumerate(data):
        path=r["vertex_sequence"];key=canonical_word(path)
        for j in range(9):
            projection=[(v&((1<<j)-1))|((v>>(j+1))<<j) for v in path]
            counts=Counter(projection);assert max(counts.values())<=2
            doubled={v for v,n in counts.items() if n==2}
            ans=decide(counts,doubled,8,2500000,True);witness=ans.pop("path")
            assert ans["status"]=="OPEN" or ans["solutions"]>=1
            if witness and ans["solutions"]==1 and ans["status"]=="FOUND":assert canonical_word(witness)==key
            if witness:found.add(canonical_word(witness))
            rows.append(dict(source=i,axis=j,doubled=len(doubled),**ans))
            hist[ans["solutions"]]+=1
        if i%20==0:save(Path("fibre-phase-bank.json"),rows)
    save(Path("fibre-phase-bank.json"),rows);print(len(rows),hist,len(found),Counter(r["status"] for r in rows))
