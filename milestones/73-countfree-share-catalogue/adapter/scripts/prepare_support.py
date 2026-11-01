"""Pin existing normalization and checked local-share bridge dependencies."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
for d in ['upstream','data','logs','build']:(HERE/d).mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();lf=lambda p:hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
OLD=ROOT/'milestones/32-seven-count-four-screen';receipt=OLD/'data/normalization-support.json'
expected=json.loads(receipt.read_text());build=Path((OLD/'build/proofs-latest.txt').read_text().strip());records=[]
for r in expected:
    name=Path(r['path']).stem;src=OLD/'upstream'/(name+'.lean');maintained=ROOT/r['path'];obj=build/(name+'.olean');log=OLD/'logs'/('support-'+name+'.log')
    assert lf(src)==r['sha256_lf']==lf(maintained)
    assert obj.exists() and log.exists()
    txt=log.read_text(encoding='utf-8-sig');assert 'error:' not in txt and 'sorryAx' not in txt
    (HERE/'upstream'/(name+'.lean')).write_bytes(src.read_bytes())
    records.append(dict(module=name,source_path=r['path'],source_sha256=sha(src),olean_path=str(obj),olean_sha256=sha(obj),inherited_log_path=str(log),inherited_log_sha256=sha(log)))
SHARE=ROOT/'milestones/72-four-count-proof-closure/critical-current/share-proof'
sr=SHARE/'data/proof-audit.json';sa=json.loads(sr.read_text());src=SHARE/'lean/LocalWindowShareBridge.lean';obj=SHARE/'build/semantic/LocalWindowShareBridge.olean';log=SHARE/'logs/LocalWindowShareBridge.log'
assert sa['status']=='PASS_LOCAL_SHARE_THEOREM' and sa['source_sha256']['LocalWindowShareBridge']==sha(src)
assert obj.exists() and log.exists()
(HERE/'upstream/LocalWindowShareBridge.lean').write_bytes(src.read_bytes())
records.append(dict(module='LocalWindowShareBridge',source_path=str(src.relative_to(ROOT)),source_sha256=sha(src),olean_path=str(obj),olean_sha256=sha(obj),inherited_log_path=str(log),inherited_log_sha256=sha(log)))
COVER=HERE.parent/'coverage';cr=COVER/'data/proof-audit.json';ca=json.loads(cr.read_text());src=COVER/'lean/SixShapeCoverage.lean';obj=COVER/'build/SixShapeCoverage.olean';log=COVER/'logs/SixShapeCoverage.log'
assert ca['status']=='PASS_SIX_TRANSITION_COVERAGE' and ca['source_sha256']==sha(src) and ca['olean_sha256']==sha(obj)
(HERE/'upstream/SixShapeCoverage.lean').write_bytes(src.read_bytes())
records.append(dict(module='SixShapeCoverage',source_path=str(src.relative_to(ROOT)),source_sha256=sha(src),olean_path=str(obj),olean_sha256=sha(obj),inherited_log_path=str(log),inherited_log_sha256=sha(log)))
out=dict(status='PINNED_SUPPORT_HASHES_MATCH',normalization_receipt_path=str(receipt),normalization_receipt_sha256=sha(receipt),share_receipt_path=str(sr),share_receipt_sha256=sha(sr),coverage_receipt_path=str(cr),coverage_receipt_sha256=sha(cr),normalization_build=str(build),share_build=str(SHARE/'build/semantic'),coverage_build=str(COVER/'build'),modules=records,scope='Existing compiled normalization, coverage and local-share bridge reused after source/artifact checks. No fresh inherited dependency rebuild.')
(HERE/'data/support.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'],len(records),'modules',flush=True)
