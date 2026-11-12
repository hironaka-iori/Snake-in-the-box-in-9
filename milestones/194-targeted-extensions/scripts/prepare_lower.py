from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
inputpath=R/'milestones/191-coloured-replacements/data/fixed26-enumeration.json'
old=json.loads(inputpath.read_text())
assert old['maximum_joined_edges']==48
path=old['joined_vertices'];assert len(path)==49
(H/'data/lower-input.json').write_text(json.dumps([dict(vertex_sequence=path)],indent=2)+'\n')
(H/'data/lower-provenance.json').write_text(json.dumps(dict(source=str(inputpath),sha256=hashlib.sha256(inputpath.read_bytes()).hexdigest(),dimension=7,edges=48,target_edges=49),indent=2)+'\n')
source=(H/'scripts/target.py').read_text()
for before,after in [("bank9-input.json","lower-input.json"),("range(512)","range(128)"),("range(9)","range(7)"),("1<<512","1<<128"),("[0,191]","[0,48]"),("191 not in blocked","48 not in blocked"),("191-length","48-length"),("len(full)==193","len(full)==50")]:
    assert before in source,before
    source=source.replace(before,after)
target=H/'scripts/lower_target.py';assert not target.exists();target.write_text(source,encoding='utf-8',newline='\n')
print('PREPARED_LOWER_DIMENSION_COMPARISON')
