"""Follow the supplied physical 190-edge control through every occupancy decision."""
import json
import random
from pathlib import Path
from model import factors,geometry
base=Path(__file__).resolve().parent
c=json.loads((base/'control.json').read_text())
path=c['witness'];geometry(path)
assert len(path)==191
target=191*c['scale']
bias,inside,ends,pool,groups=factors(c)
scopes=[s for s,o in groups];opts=[[tuple(x) for x in o] for s,o in groups]
where={v:[(j,1<<cell.index(v)) for j,cell in enumerate(scopes) if v in cell] for v in pool}
order=sorted(pool);random.Random(204829).shuffle(order)
bound=lambda:bias+sum(max(val for k,val in options) for options in opts)
genuine=set(path)-inside
def descend(i,fh):
    assert bound()>=target
    if i==len(order):
        assert bound()==target
        print('H',len(path),*path,file=fh)
        return
    v=order[i];print('S',v,file=fh)
    inc=where[v];old=[opts[j] for j,b in inc]
    for bit in [0,1]:
        for (j,b),items in zip(inc,old):
            opts[j]=[(k,val) for k,val in items if bool(k&b)==bit]
        if (v in genuine)==bit:descend(i+1,fh)
        else:
            score=bound() if all(opts[j] for j,b in inc) else -100000000
            print('B' if score<target else 'O',score,file=fh)
        for (j,b),items in zip(inc,old):opts[j]=items
with (base/'control_unpinned.tree').open('w') as out:descend(0,out)
