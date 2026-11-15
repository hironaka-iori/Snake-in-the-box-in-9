"""Record necessary exact-two allocations for the still-open contexts; no search."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
rp=H/'data/regions46.json';fp=H/'data/free-summary.json';raw=json.loads(rp.read_bytes());frontier=json.loads(fp.read_bytes())
rows=[]
for ident in frontier['unresolved']:
    c=raw['contexts'][ident];fixed=4-c['replacement_crossings'];budget=2-fixed;choices=[]
    for p in c['parts']:
        u,v=p['anchors'];parity=int((u<256)!=(v<256))
        choices.append([a for a in range(parity,budget+1,2) if a!=0 or sum((x<256)==(u<256) for x in p['allowed'])>=47])
    allocations=[[a,b] for a in choices[0] for b in choices[1] if a+b==budget]
    expected=[sum(x>=256 for x in p['anchors']) for p in c['parts']]
    assert allocations==[expected] and expected in [[0,0],[1,0]]
    rows.append(dict(context=ident,intervals=c['intervals'],fixed_crossings=fixed,replacement_budget=budget,allocations=allocations))
assert len(rows)==11 and sum(r['allocations']==[[0,0]] for r in rows)==4
out=dict(status='NECESSARY_ALLOCATION_TARGETS_ONLY',total_crossings=2,contexts=rows,pins={str(p):sha(p) for p in [rp,fp,Path(__file__)]},scope='Parity/capacity reasoning only for the11 open width46contexts. No two-crossing path-pair preparation or solver query has been run. Four cases have both replacements lower; seven have one crossing in the first replacement and zero in the second. No boundary-change cut is justified by the four/six-crossing covers. Counts>=8 are not ruled out in these contexts.')
(H/'data/two-crossing-frontier.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PREPARED_TWO_CROSSING_TARGETS',len(rows))
