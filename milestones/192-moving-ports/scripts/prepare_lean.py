from pathlib import Path
import hashlib,json
R=Path('E:/Snake-in-a-box');H=R/'milestones/192-moving-ports';P=R/'milestones/191-coloured-replacements';D=Path(__file__).parent
names=['MovingEndpoints192','EndpointAttachments192'];sources={}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in names:
    q=H/'lean'/(name+'.lean');q.write_bytes((D/(name+'.lean')).read_bytes());sources[name]=sha(q)
pins={str(H/'scripts/native_resources.py'):sha(H/'scripts/native_resources.py')};parents=[R/'milestones/190-exchange-constraints',P]
for parent,mods in [(parents[0],['EdgeData190','EdgeBalance190','IncidenceBalance190']),(parents[1],['AttachmentBalance191','AlternatingCounts191'])]:
    for name in mods:
        path=parent/'data'/(name+'-audit.json');j=json.loads(path.read_text());assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
        pins[str(path)]=sha(path);pins[str(j['object'])]=j['olean_sha256']
        for p,h in j['dependencies'].items():assert sha(p)==h; pins[p]=h
        assert sha(j['object'])==j['olean_sha256']
base=json.loads((P/'data/AttachmentBalance191-execution.json').read_text());base.update(new_module_order=names,source_sha256=sources,input_pins=pins,checker_sha256=sha(H/'scripts/check_core.py'),search_paths=[str(H/'build')]+[str(p/'build') for p in parents])
for name in names:(H/'data'/(name+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(names,indent=2)+'\n');(H/'scripts/prepare_lean.py').write_bytes(Path(__file__).read_bytes())
