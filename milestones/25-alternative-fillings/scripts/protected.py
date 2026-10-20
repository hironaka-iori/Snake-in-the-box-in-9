"""Retain the changed endpoint while repairing different coordinate faces."""
import json
from pathlib import Path
import search
original=search.build
protected_vertex=12
def build(n,seed,inside,target):
    m,x,starts,arcs,g=original(n,seed,inside,target)
    if protected_vertex in x:m.add(x[protected_vertex]==1)
    elif protected_vertex not in g['internal']:m.add_bool_or([])
    return m,x,starts,arcs,g
search.build=build
def main():
    datafile=search.HERE/'data/results.json';data=json.loads(datafile.read_text())
    seed=data['runs'][5]['path_vertices']
    assert protected_vertex in seed and data['runs'][5]['target_edges']==190
    inventory=search.ROOT/'milestones/23-parity-compatible-faces/data/boundary-inventory.json'
    faces={r['face_index']:r for r in json.loads(inventory.read_text())['rows']}
    report=dict(script_sha256_lf=search.sha(Path(__file__)),
        search_sha256_lf=search.sha(Path(search.__file__)),parent_sha256_lf=search.sha(datafile),
        protected_vertex=protected_vertex,parent_run=5,
        scope='Required selected vertex, not a required endpoint. Restricted exact-length searches; no global exclusion.',runs=[])
    for fi in [0,3,4,5]:
        f=faces[fi];inside={v for v in range(512) if v&f['fixed_mask']==f['fixed_value']}
        for target in [191,192]:
            r=search.solve(9,seed,inside,target,20);r['face_index']=fi
            if 'path_vertices' in r:assert protected_vertex in r['path_vertices']
            report['runs'].append(r)
            (search.HERE/'data/protected.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
            print(json.dumps({k:r.get(k) for k in ['face_index','target_edges','status','objective_new_vertices']}),flush=True)
            if r.get('target_edges')==192 and 'path_vertices' in r:return
if __name__=='__main__':main()
