from pathlib import Path
import json,hashlib
R=Path('E:/Snake-in-a-box');H=R/'milestones/190-exchange-constraints';P=R/'milestones/189-middle-replacements'
for n in ['data','scripts','lean','build','logs','sources']:(H/n).mkdir(parents=True,exist_ok=True)
(H/'.gitattributes').write_text('* -text\n')
for n in ['check_core.py','native_resources.py']:(H/'scripts'/n).write_bytes((P/'scripts'/n).read_bytes())
row=json.loads((P/'data/replacement-contexts.json').read_text())['rows'][0]
(H/'data/middle95.json').write_text(json.dumps({'middle':row['middle'],'ports':row['ports'],'source':str(P/'data/replacement-contexts.json'),'source_sha256':hashlib.sha256((P/'data/replacement-contexts.json').read_bytes()).hexdigest()},indent=2)+'\n')
s=(P/'scripts/edit_neighbourhood.py').read_text().replace("H=R/'milestones/189-middle-replacements'","H=R/'milestones/190-exchange-constraints'").replace("row=json.loads((H/'data/replacement-contexts.json').read_text())['rows'][0]","row=json.loads((H/'data/middle95.json').read_text())")
s=s.replace('model.add(x[s]==1);', '''# Exact degree and edge accounting for a fixed-endpoint replacement.
deleted_pair=[]
for i,(u,v) in enumerate(zip(old,old[1:])):
    z=model.new_bool_var('deleted_pair'+str(i));model.add(z<=1-x[u]);model.add(z<=1-x[v]);model.add(z>=1-x[u]-x[v]);deleted_pair.append(z)
oldset=set(old)
added_edges=[b for (u,v),b in directed.items() if u not in oldset and v not in oldset]
model.add(sum(added_edges)==sum(deleted_pair)+2)
model.add(x[s]==1);''')
s=s.replace("'status':solver.status_name(status)","'status':solver.status_name(status),'exchange_edge_identity_imposed':True")
s=s.replace('random_seed=189','random_seed=190')
(H/'scripts/edit_neighbourhood.py').write_text(s,encoding='utf-8',newline='\n');(H/'scripts/prepare.py').write_bytes(Path(__file__).read_bytes())
