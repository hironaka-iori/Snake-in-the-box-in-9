"""Find three disjoint regions each attached through one outside vertex."""
from pathlib import Path
import hashlib,itertools,json
H=Path(__file__).resolve().parents[1];source=H/'data/colour-survey.json';raw=json.loads(source.read_bytes())
done=set()
for name in ['cut-certificates','endpoint-separators']:
    for r in json.loads((H/'data'/(name+'.json')).read_bytes())['rows']:
        if 'cut' in r:done.add(r['id'])
rows=[]
for g in raw['survivors']:
    if g['id'] in done:continue
    U=set(g['vertices']);adj={v:set() for v in U}
    for v,w,z in g['edges']:adj[v].add(w);adj[w].add(v)
    regions=[]
    for a in sorted(U):
        remaining=U-{a};cs=[]
        while remaining:
            todo=[min(remaining)];c=set()
            while todo:
                v=todo.pop()
                if v in c:continue
                c.add(v);remaining.remove(v);todo.extend((adj[v]&remaining)-c)
            cs.append(c)
        if len(cs)>1:
            for c in cs:regions.append((a,c))
    triple=next((ts for ts in itertools.combinations(regions,3) if all(not x[1]&y[1] for x,y in itertools.combinations(ts,2))),None)
    rows.append(dict(id=g['id'],regions=[dict(attachment=a,vertices=sorted(c)) for a,c in triple]) if triple else dict(id=g['id'],status='NO_THREE_LEAF_REGIONS'))
out=dict(status='COMPLETE',rows=rows,certified=sum('regions' in r for r in rows),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Each nonempty proper region whose only outside neighbour is one attachment vertex must contain a Hamiltonian-path endpoint: otherwise the path enters and exits through the same vertex. Three disjoint such regions require three endpoints. Native graph-certificate extraction, with written proof.')
(H/'data/leaf-components.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('THREE_LEAF_REGION_CERTIFICATES',out['certified'],'of',len(rows))
