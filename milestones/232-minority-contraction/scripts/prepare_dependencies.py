from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
sources={'LayerJoining':R/'milestones/231-endpoint-exchanges/data/LayerJoining-audit.json','ColourContraction231':R/'milestones/231-endpoint-exchanges/data/ColourContraction231-audit.json','TwoCrossings188':R/'milestones/188-dimensional-constructions/data/TwoCrossings188-audit.json'}
for name,p in sources.items():
    a=json.loads(p.read_bytes());assert a['status']=='PASS'
    assert all(sha(q)==h for q,h in a['dependencies'].items())
    for key,hashkey in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(a[key])==a[hashkey]
    (H/'lean'/(name+'.lean')).write_bytes(Path(a['source']).read_bytes());(H/'build'/(name+'.olean')).write_bytes(Path(a['object']).read_bytes());(H/'data'/(name+'-audit.json')).write_bytes(p.read_bytes())
print('THREE_ACCEPTED_DEPENDENCIES_COPIED')
