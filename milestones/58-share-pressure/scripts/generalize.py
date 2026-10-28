"""Test two joint-count share hypotheses covering the current critical family."""
from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
import direct
original=direct.model
cases=[dict(name='triple11',dirs=[0,1,2,3,0,4],alpha=[[1,5],[6,21],[1,5],[1,5],[6,21]],joint_positions=[1,3,4],joint_cap=11,cap=95),
       dict(name='quadruple13',dirs=[0,1,2,3,0,1],alpha=[[1,5],[1,5],[6,21],[1,5],[1,5]],joint_positions=[1,2,4,5],joint_cap=13,cap=95)]
if '--weak' in sys.argv:
    cases=[dict(c,name=c['name']+'_share24',cap=23) for c in cases]
if '--universal' in sys.argv:
    cases=[dict(c,name=c['name']+'_no_count_caps_share24',alpha=[[1,21]]*5,joint_positions=[],joint_cap=0,cap=23) for c in cases]
active=None
def joint_model(*args,**kwargs):
    md,x,total,win,B,cuts=original(*args,**kwargs)
    prefixes=[f'alpha{win[p]}_' for p in active['joint_positions']]
    indices=[i for i,var in enumerate(md.proto.variables) if any(var.name.startswith(prefix) for prefix in prefixes)]
    assert len(indices)==36*len(prefixes)
    md.add(sum(md.get_bool_var_from_proto_index(i) for i in indices)<=active['joint_cap'])
    return md,x,total,win,B,cuts
direct.model=joint_model
(HERE/'data/generalized').mkdir(exist_ok=True)
for case in cases:
    active=case
    path=HERE/f"data/generalized/{case['name']}.json"
    if path.exists():continue
    result=direct.solve(case,seconds=20)
    if result['status']=='FEASIBLE':
        assert sum(result['census']['alpha'][p-1] for p in case['joint_positions'])<=case['joint_cap']
    result['scope']='Numerical joint-count share hypothesis; no Lean proof. Any positive assignment is a local forest only.'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(case['name'],result['status'],result.get('census'),flush=True)
