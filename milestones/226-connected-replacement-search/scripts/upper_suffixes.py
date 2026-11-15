"""Enumerate complete upper suffixes of one-crossing first replacements."""
from pathlib import Path
import json,hashlib,collections
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=H/'data/regions44.json';raw=json.loads(source.read_bytes());result=H/'data/boundary44.json'
ids=[r['id'] for r in json.loads(result.read_bytes())['results'] if r['status']=='UNKNOWN']
rows=[]
for ident in ids:
    row=raw['contexts'][ident];part=row['parts'][0];u,v=part['anchors']
    if (u^v)&256==0:continue
    assert u<256<=v
    other=row['parts'][1];x,y=other['anchors'];parity=((x^y)>>8)&1
    minimum=parity
    if parity==0 and sum((z&256)==(x&256) for z in other['allowed'])<45:minimum=2
    assert row['replacement_crossings']-minimum==1
    upper={z for z in part['allowed'] if z>=256};lower=set(part['allowed'])-upper
    stack=[[v]];suffixes=[];nodes=0
    while stack:
        path=stack.pop();nodes+=1
        if path[-1]^256 in lower:
            suffixes.append(dict(vertices=list(reversed(path)),lower_port=path[-1]^256,lower_vertices=45-len(path),lower_edges=44-len(path)))
        for z in sorted(upper-set(path)):
            if (z^path[-1]).bit_count()==1 and all((z^t).bit_count()!=1 for t in path[:-1]):stack.append(path+[z])
    rows.append(dict(id=ident,intervals=row['intervals'],first_anchors=[u,v],allocation=[1,minimum],upper_domain=sorted(upper),prefix_nodes=nodes,suffixes=suffixes))
assert len(rows)==11 and all(r['prefix_nodes']==2 and [s['vertices'] for s in r['suffixes']]==[[480],[488,480]] for r in rows)
out=dict(status='COMPLETE_FINITE_ENUMERATION',contexts=rows,pins={str(source):sha(source),str(result):sha(result),str(Path(__file__)):sha(Path(__file__))},scope='For the11still-open44contexts whose first anchor faces differ, crossing parity and the second face shortage force exactlyone first crossing. Enumerating every induced upper suffix to its terminal anchor gives two possibilities. Native geometric enumeration; no actual lower-path pair or new snake is asserted.')
(H/'data/upper-suffixes.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('COMPLETE_UPPER_SUFFIXES',len(rows),'contexts; ports224/232; lower edge lengths43/42')
