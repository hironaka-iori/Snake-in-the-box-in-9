"""Pin the inherited proof environment and port small, closed credit roots."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
(HERE/'.gitattributes').write_text('* -text\n')
old=ROOT/'milestones/97-geometric-credit-integration'
paths=read(old/'data/GeometricAssembly97-audit.json')['paths']
extra=[];receipts={};objects={};sources={}
for dirname in ['51-exact-bucket-pressure','52-share-on-235','53-shares-on-sat-obstruction']:
    base=ROOT/'milestones'/dirname;rpath=base/'data/verification.json';r=read(rpath)
    assert r['status']=='PASS'
    receipts[rpath.relative_to(ROOT).as_posix()]=sha(rpath)
    build=Path((base/'build/latest.txt').read_text().strip());extra.append(str(build))
    for name,digest in r['source_hashes'].items():
        src=base/'lean'/(name+'.lean');assert sha(src)==digest,name
        obj=build/(name+'.olean');assert obj.is_file(),name
        sources[src.relative_to(ROOT).as_posix()]=digest
        objects[obj.relative_to(ROOT).as_posix()]=sha(obj)
base=ROOT/'milestones/73-countfree-share-catalogue';rpath=base/'data/integration-audit.json';r=read(rpath)
assert r['status']=='PASS_COMBINED_LOCAL_CATALOGUE_AND_BUDGET'
receipts[rpath.relative_to(ROOT).as_posix()]=sha(rpath)
combined=base/'build/combined'
for row in r['overlay_objects']:
    obj=combined/row['module'];assert sha(obj)==row['object_sha256'],str(obj)
    objects[obj.relative_to(ROOT).as_posix()]=row['object_sha256']
specs=[('Port98M51SharePressure','51-exact-bucket-pressure','SharePressure'),
       ('Port98M52SharePressure','52-share-on-235','SharePressure'),
       ('Port98M53ShareBound0','53-shares-on-sat-obstruction','ShareBound0'),
       ('Port98M53ShareBound5','53-shares-on-sat-obstruction','ShareBound5'),
       ('Port98CombinedCatalogue','73-countfree-share-catalogue','CombinedCatalogue')]
ports=[]
for module,dirname,original in specs:
    src=ROOT/'milestones'/dirname/'lean'/(original+'.lean')
    dest=HERE/'lean'/(module+'.lean');dest.write_bytes(src.read_bytes())
    ports.append(dict(module=module,original=src.relative_to(ROOT).as_posix(),source=dest.relative_to(ROOT).as_posix(),sha256=sha(src)))
paths=[str(HERE/'build'),*paths,str(combined),*extra]
assert len(paths)==len(set(paths))
env=dict(status='PINNED_REUSED_OBJECT_ENVIRONMENT',paths=paths,receipts=receipts,sources=sources,objects=objects,ports=ports,
    scope='Existing successful proof closures and exact object bytes reused. Fresh small-root and combined-import checks remain required. No complete clean rebuild is asserted.')
(HERE/'data/environment.json').write_text(json.dumps(env,indent=2)+'\n')
print('PINNED_ENVIRONMENT',len(objects),'objects;',len(sources),'historical sources;',len(ports),'ports')
