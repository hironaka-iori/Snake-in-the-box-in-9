"""Look for fresh 191-edge witnesses on reconnected projections; try both tips."""
import json
from pathlib import Path
from search_q9_flexible_corners import solve
from search_q9_two_flexible_ends import verify


def sym_key(steps):
    def norm(word):
        perm={}
        return tuple(perm.setdefault(x,len(perm)) for x in word)
    return min(norm(steps),norm(steps[::-1]))

if __name__=="__main__":
    known = set()
    for l in Path("/tmp/q9_project_records_input9").read_text().splitlines():
        dim,*seq=map(int,l.split())
        assert dim==9 and len(seq)==191
        known.add(sym_key(seq))
    assert len(known)==131
    rows=[json.loads(l) for l in open("q9_projected_reversal_192.jsonl")]
    rows.sort(key=lambda r:r[0]!="UNKNOWN")
    for _,_,_,_,key,_ in rows[:1500]:
        p=bytes.fromhex(key)
        ids=list(range(1,len(p)-1,2))
        s,w=solve(p,[],ids,191,5000,True)
        novel=False
        winner=None
        if w:
            verify(w,191)
            seq=[(a^b).bit_length()-1 for a,b in zip(w,w[1:])]
            novel=sym_key(seq) not in known
            if len(w)>=193:winner=w
            for a in (w,w[::-1]):
                for i in range(9):
                    v=a[-1]^(1<<i)
                    if v in a or any((v^u).bit_count()==1 for u in a[:-1]):continue
                    winner=a+[v]
            if winner:verify(winner,192)
        print(json.dumps([s,key,novel,w,winner],separators=(",",":")),flush=True)
        if winner:break
