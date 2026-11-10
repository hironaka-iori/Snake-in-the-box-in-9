from pathlib import Path
import gzip,json,collections,hashlib
H=Path('E:/Snake-in-a-box/milestones/187-clause-interpretation')
R=H.parents[1]
j=json.loads(gzip.decompress((H/'contributors/milestones/31-233-cost/data/keys233_best.json.gz').read_bytes()))
out={}
for q in [4,5]:
    rows=[r for r in j['share'] if r[4]!='lean_floor' and tuple(r[0]) in {(0,1,2,3,1,0),(0,1,2,3,4,5)} and 0<r[2]-q<=12]
    out[str(q)]={'additional_rows':len(rows),'rows':rows}
prior=R/'milestones/73-countfree-share-catalogue'
audit=json.loads((prior/'data/integration-audit.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(prior/'lean/CombinedCatalogue.lean')==audit['source_sha256']
records=[]
for name,root in [('Share12/Geometry',R/'milestones/72-four-count-proof-closure/critical-current/share-proof'),('Share7305/Reversal',prior/'cases/case7305')]:
    record=next(r for r in audit['overlay_objects'] if r['module']==name+'.olean')
    src=root/'lean'/(name+'.lean');obj=root/'build/semantic'/(name+'.olean')
    assert sha(src)==record['source_sha256'] and sha(obj)==record['object_sha256']
    records.append({'source':str(src),'source_sha256':sha(src),'object':str(obj),'object_sha256':sha(obj)})
out['evidence']={'integration_receipt':str(prior/'data/integration-audit.json'),'receipt_sha256':sha(prior/'data/integration-audit.json'),'checked_source_and_object_hashes':records,'full_independent_dependency_rebuild':False}
out['combined_counts']={q:{'remaining_with_existing_floors':426,'remaining_with_critical_floor15':373 if q=='4' else 366} for q in ['4','5']}
out['note']='33 additional rows use the two recorded universal share-12 theorems; 16 already follow at the original level, and 17 need the new slack. The relaxed table coverage remains unproved in Lean.'
(H/'data/floor12-census.json').write_text(json.dumps(out,indent=2)+'\n')
(H/'scripts/floor12_census.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({q:{'additional_rows':out[q]['additional_rows']} for q in ['4','5']}))
