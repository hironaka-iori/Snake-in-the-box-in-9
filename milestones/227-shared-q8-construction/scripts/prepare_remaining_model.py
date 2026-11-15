"""Specialize the audited pair model to the remaining zero-crossing first paths."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1]
s=(H/'scripts/pair_cp.py').read_text(encoding='utf-8')
reps=json.loads((H/'data/remaining-companions.json').read_bytes())['representatives']
changes=[
("default='0,1,14,15,16'",'default='+repr(','.join(map(str,reps)))),
("data/companions.json","data/remaining-companions.json"),
("edges=[43,c['lower_edges']];anchors=[(18,224),(u,v)]", "edges=[c['first_edges'],c['lower_edges']];anchors=[tuple(c['first_anchors']),(u,v)]\n    f0,f1=anchors[0]"),
("set(c['lower_domain'])-({18,224}|N[18]|N[224])", "set(c['lower_domain'])-({f0,f1}|N[f0]|N[f1])"),
("model=cp_model.CpModel();variables=[]", "if any(not set(pair)<=domain for pair,domain in zip(anchors,domains)):\n        result['results'].append(dict(id=ident,status='STATIC_INFEASIBLE',reason='Mandatory anchors conflict',seconds=0.0));save(out/'result.json',result);continue\n    model=cp_model.CpModel();variables=[]"),
("first=p+[480];second=", "first=p;second=")]
for old,new in changes:assert s.count(old)==1,(old,s.count(old));s=s.replace(old,new)
p=H/'scripts/remaining_cp.py';assert not p.exists();p.write_text(s,encoding='utf-8')
runner=(H/'scripts/run_pair_cp.py').read_text(encoding='utf-8').replace('pair_cp.py','remaining_cp.py').replace('data/companions.json','data/remaining-companions.json')
(H/'scripts/run_remaining.py').write_text(runner,encoding='utf-8')
print('PREPARED',len(reps),'REPRESENTATIVES')
