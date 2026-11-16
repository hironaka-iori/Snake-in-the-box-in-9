"""Use the forced endpoints to strengthen the saved small separators."""
from pathlib import Path
import hashlib,itertools,json,time
H=Path(__file__).resolve().parents[1];source=H/'data/colour-survey.json';raw=json.loads(source.read_bytes())
old=json.loads((H/'data/cut-certificates.json').read_bytes());done={r['id'] for r in old['rows'] if 'cut' in r};rows=[];start=time.monotonic()
for g in raw['survivors']:
    if g['id'] in done:continue
    U=set(g['vertices']);adj={v:set() for v in U};ends=set(g['leaves'])
    if len(ends)!=2:
        rows.append(dict(id=g['id'],status='ENDPOINTS_NOT_FORCED',leaf_count=len(ends)));continue
    for u,v,z in g['edges']:adj[u].add(v);adj[v].add(u)
    found=None
    for size in [1,2]:
        for cut in itertools.combinations(sorted(U),size):
            S=set(cut);remaining=U-S;cs=[]
            while remaining:
                todo=[min(remaining)];c=set()
                while todo:
                    v=todo.pop()
                    if v in c:continue
                    c.add(v);remaining.remove(v);todo.extend((adj[v]&remaining)-c)
                cs.append(sorted(c))
            if len(cs)>size+1-len(S&ends):reason='ENDPOINT_RUN_BUDGET'
            elif len(cs)==size+1 and not S&ends and any(ends<=set(c) for c in cs):reason='ENDPOINTS_IN_ONE_COMPONENT'
            else:continue
            found=dict(id=g['id'],cut=list(cut),endpoints=sorted(ends),components=cs,reason=reason);break
        if found:break
    rows.append(found or dict(id=g['id'],status='NO_ENDPOINT_SEPARATOR'))
result=dict(status='COMPLETE',rows=rows,certified=sum('cut' in x for x in rows),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),prior_sha256=hashlib.sha256((H/'data/cut-certificates.json').read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,scope='The two graph leaves must be Hamiltonian endpoints. Deleting S leaves at most |S|+1-|S intersect endpoints| nonempty path segments. If there are |S|+1 graph components and endpoints outsideS lie in one component, that component needs two distinct segments, which exceeds the bound. Finite certificates and graph extraction remain native.')
(H/'data/endpoint-separators.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('ADDITIONAL_ENDPOINT_SEPARATORS',result['certified'],'of',len(rows),'seconds',result['seconds'])
