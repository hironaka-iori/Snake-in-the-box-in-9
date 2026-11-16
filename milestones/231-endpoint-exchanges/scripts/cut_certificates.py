"""Seek elementary separators for the49 excluded Hamiltonian candidates."""
from pathlib import Path
import hashlib,itertools,json,time
H=Path(__file__).resolve().parents[1]
source=H/'data/colour-survey.json';raw=json.loads(source.read_bytes());out=[];start=time.monotonic()
for g in raw['survivors']:
    U=set(g['vertices']);adj={v:set() for v in U}
    for u,v,z in g['edges']:adj[u].add(v);adj[v].add(u)
    def components(cut):
        remaining=U-set(cut);result=[]
        while remaining:
            todo=[min(remaining)];c=set()
            while todo:
                v=todo.pop()
                if v in c:continue
                c.add(v);remaining.remove(v);todo.extend((adj[v]&remaining)-c)
            result.append(sorted(c))
        return result
    found=None
    for size in [1,2]:
        for cut in itertools.combinations(sorted(U),size):
            cs=components(cut)
            if len(cs)>size+1:
                found=dict(id=g['id'],cut=list(cut),components=cs);break
        if found:break
    out.append(found or dict(id=g['id'],status='NO_SMALL_SEPARATOR'))
result=dict(status='COMPLETE',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),rows=out,certified=sum('cut' in r for r in out),seconds=time.monotonic()-start,scope='A graph with Hamiltonian path has at most |S|+1 components after deleting S. Only cuts of size1or2 were considered. No certificate found does not mean Hamiltonicity.')
(H/'data/cut-certificates.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('SMALL_SEPARATOR_CERTIFICATES',result['certified'],'of',len(out),'seconds',result['seconds'])
