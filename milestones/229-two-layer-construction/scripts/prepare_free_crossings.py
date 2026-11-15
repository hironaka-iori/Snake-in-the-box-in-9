"""Remove the prescribed crossing count while retaining the construction family."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
s=(H/'scripts/joint_six.py').read_text(encoding='utf-8')
s=s.replace("    row=dict(row);row['replacement_crossings']+=2\n",'')
old="half=model.new_int_var(0,row['replacement_crossings']//2,f'cross_pairs{k}')"
assert s.count(old)==1;s=s.replace(old,"half=model.new_int_var(0,len(edges)//2,f'cross_pairs{k}')")
old="    model.add(sum(all_cross_edges)==row['replacement_crossings'])\n"
assert s.count(old)==1;s=s.replace(old,'')
old="        assert sum(u^v==256 for u,v in zip(path,path[1:]))==6\n"
assert s.count(old)==1;s=s.replace(old,"        actual_crossings=sum(u^v==256 for u,v in zip(path,path[1:]))\n")
s=s.replace("out['witness']=dict(context=row['id'],path=path,replacements=routes)","out['witness']=dict(context=row['id'],path=path,replacements=routes,total_bit8_crossings=actual_crossings)")
old='The final snake has six bit8crossings; the original fixed-crossing count is preserved, so each prepared replacement budget is increased by two.'
assert old in s;s=s.replace(old,'No total crossing count is prescribed. Per-part crossing parity and same-face capacity minima remain necessary; the parity variable bound uses the actual number of available vertical edges, not a saved crossing budget.')
p=H/'scripts/joint_free.py';assert not p.exists();p.write_text(s,encoding='utf-8')
s=(H/'scripts/run_six.py').read_text(encoding='utf-8').replace('joint_six.py','joint_free.py')
(H/'scripts/run_free.py').write_text(s,encoding='utf-8')
j=json.loads((H/'data/six-crossing-plan.json').read_bytes())
out=dict(status='PREPARED_UNEXECUTED',width=46,total_crossings=None,ids=j['ids'],static_exclusions=j['static_exclusions'],pins={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [H/'data/regions46.json',H/'scripts/joint_free.py',H/'scripts/run_free.py',Path(__file__)]},scope='Any total crossing count. Same seed, append24, two width46 length-preserving replacement blocks and retained anchors/outside positions. Initial domains/static exclusions are crossing-independent. No boundary-change cut or prior-width exclusion. All209pendingcontexts planned; complete193vertex inducedness audit required for each candidate.')
(H/'data/free-crossing-plan.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PREPARED_FREE_CROSSING_QUERIES',len(out['ids']))
