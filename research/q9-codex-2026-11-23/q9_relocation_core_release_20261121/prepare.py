from pathlib import Path
import json
B=Path(__file__).resolve().parent; R=B.parent
src=[json.loads(l) for l in (R/'q9_endpoint_graph_cp_20261121/branch_manifest.jsonl').read_text().splitlines()]
bank=(R/'q9_far189_spring_20261121/comparison191.words').read_text().split()
def path(w):
    p=[0]
    for c in w:p.append(p[-1]^(1<<int(c)))
    return p
def geometry(p):
    assert len(p)==len(set(p)) and all(((a^b).bit_count()==1)==(j==i+1) for i,a in enumerate(p) for j,b in enumerate(p) if i<j)
def info(r):
    p=path(bank[r['archive']]);ep=p[-1] if r['side'] else p[0];y=r['new_vertex']
    blockers={v for v in p if v!=ep and (v^y).bit_count()==1}
    fixed={v for v in p if min((v^u).bit_count() for u in blockers)>3}|{ep}
    return r|dict(ep=ep,forbidden=sorted(blockers),oldfixed=sorted(fixed))
ranks=[0,2,4,8,12,36,96,111]
if __name__=='__main__':
    rows=[info(src[i]) for i in ranks];(B/'branches.json').write_text(json.dumps(rows))
    with (B/'branches.txt').open('w') as f:
        for r in rows:
            z=r['forbidden'];a=r['oldfixed'];print(r['rank'],r['ep'],r['new_vertex'],len(z),len(a),*z,*a,file=f)
