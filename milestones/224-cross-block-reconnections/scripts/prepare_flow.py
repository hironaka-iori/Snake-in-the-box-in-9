"""Add necessary single-source connectivity flows in selected open regions."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
raw=json.loads((H/'data/regions44-refined.json').read_bytes())
ranked=sorted(raw['contexts'],key=lambda r:(-sum(len(p['allowed']) for p in r['parts']),r['id']))
selected=[];starts=set()
for row in ranked:
    first=row['intervals'][0][0]
    if first not in starts:selected.append(row);starts.add(first)
for row in ranked:
    if len(selected)>=16:break
    if row not in selected:selected.append(row)
raw['contexts']=selected
raw['scope']='Sixteen selected unresolved44-edge contexts. Selection prioritizes distinct first-window starts then larger total domains. Add necessary connectivity flow to both replacement paths. Other unresolved contexts are untouched.'
raw['selection_ids']=[r['id'] for r in selected]
raw['selection_source_sha256']=hashlib.sha256((H/'data/regions44-refined.json').read_bytes()).hexdigest()
p=H/'data/regions44-flow.json';assert not p.exists();p.write_text(json.dumps(raw,indent=2)+'\n',encoding='utf-8')
s=(H/'scripts/joint_regions44.py').read_text(encoding='utf-8').replace("H/'data/regions44.json'","H/'data/regions44-flow.json'")
s=s.replace('All maximal contexts covering blockers7/143.','Sixteen selected unresolved contexts with explicit connectivity flows.')
insertion='''        flow={}
        for z in values:
            for w in N[z]:
                if w in x:
                    f=model.new_int_var(0,44,f'flow{k}_{z}_{w}')
                    model.add(f<=44*x[z]);model.add(f<=44*x[w]);flow[z,w]=f
        for z in values:
            model.add(sum(flow[w,z]-flow[z,w] for w in N[z] if w in x)==(-44 if z==u else x[z]))
'''
s=s.replace('        edges=[]\n',insertion+'        edges=[]\n')
(H/'scripts/joint_regions44_flow.py').write_text(s,encoding='utf-8')
s=(H/'scripts/run_regions44.py').read_text(encoding='utf-8').replace('scripts/joint_regions44.py','scripts/joint_regions44_flow.py').replace("H/'data/regions44.json'","H/'data/regions44-flow.json'")
(H/'scripts/run_regions44_flow.py').write_text(s,encoding='utf-8')
print(json.dumps(dict(selected=raw['selection_ids'],count=len(selected))),flush=True)
