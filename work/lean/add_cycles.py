from pathlib import Path
import json,runpy
d=runpy.run_path('work/lean/degree_cnf.py');r=d['r'];x=d['variables']
ns={v:{w for w in r if (v^w).bit_count()==1} for v in r}
cycles=[]
def visit(path):
    root=path[0];v=path[-1]
    for w in ns[v]:
        if w<=root or w in path:continue
        earlier=ns[w].intersection(path[:-1])
        if earlier=={root}:
            if len(path)>=5 and path[1]<w:cycles.append(path+[w])
        elif not earlier and len(path)<9:visit(path+[w])
for v in r:visit([v])
data=json.loads(Path('work/lean/totalizer112_82.json').read_text())
data['clauses'] += [[-x[v] for v in c] for c in cycles]
data['reasons']=[None]*len(data['clauses'])
data['cycles']=cycles
p=Path('work/lean/cycles112')
p.with_suffix('.json').write_text(json.dumps(data))
p.with_suffix('.cnf').write_text(f'p cnf {data["variables"]} {len(data["clauses"])}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in data['clauses']))
print('extra cycles',len(cycles),'clauses',len(data['clauses']),flush=True)
