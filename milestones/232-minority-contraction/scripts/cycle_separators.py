"""Elementary necessary separator conditions for the augmented cycle graph."""
from pathlib import Path
import hashlib,itertools,json,time
H=Path(__file__).resolve().parents[1];source=H/'data/minority.json';raw=json.loads(source.read_bytes());bases=json.loads((H/'data/bases.json').read_bytes())['bases'];rows=[];start=time.monotonic()
for row in raw['results']:
    if row['status']!='INFEASIBLE':continue
    U=set(bases[row['id']]['vertices'])|{512};adj={v:set() for v in U}
    for v,w,z in row['edges']:adj[v].add(w);adj[w].add(v)
    for p in row['ports']:v=int(p);adj[512].add(v);adj[v].add(512)
    found=None
    for size in [1,2]:
        for cut in itertools.combinations(sorted(U),size):
            remaining=U-set(cut);cs=[]
            while remaining:
                todo=[min(remaining)];c=set()
                while todo:
                    v=todo.pop()
                    if v in c:continue
                    c.add(v);remaining.remove(v);todo.extend((adj[v]&remaining)-c)
                cs.append(sorted(c))
            if len(cs)>size:found=dict(id=row['id'],cut=list(cut),components=cs);break
        if found:break
    rows.append(found or dict(id=row['id'],status='NO_SMALL_SEPARATOR'))
out=dict(status='COMPLETE',rows=rows,certified=sum('cut' in r for r in rows),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,scope='Join dummy512 to every eligible endpoint port. A Hamiltonian cycle loses at most |S| path pieces after deleting a nonempty S, so more than |S| graph components is impossible. Searches only |S|1or2; native finite certificates with written mathematical justification.')
(H/'data/cycle-separators.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print('CYCLE_SEPARATOR_CERTIFICATES',out['certified'],'of',len(rows),'seconds',out['seconds'])
