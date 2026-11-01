"""Pin and check the normalization support before reusing its compiled modules."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
for d in ['upstream','data','logs','build']:(HERE/d).mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lf=lambda p:hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
OLD=ROOT/'milestones/32-seven-count-four-screen'
receipt=OLD/'data/normalization-support.json'
expected={Path(r['path']).stem:r for r in json.loads(receipt.read_text())}
build=Path((OLD/'build/proofs-latest.txt').read_text().strip())
names=['WindowAutomatonDefs','WindowAutomatonData','WindowAutomatonLemmas','WindowAutomatonSequence','WindowAutomatonBridge']
records=[]
for name in names:
    src=OLD/'upstream'/(name+'.lean');maintained=ROOT/expected[name]['path'];obj=build/(name+'.olean');log=OLD/'logs'/('support-'+name+'.log')
    assert lf(src)==expected[name]['sha256_lf']==lf(maintained)
    assert obj.exists() and log.exists()
    txt=log.read_text(encoding='utf-8-sig')
    assert 'error:' not in txt and 'sorryAx' not in txt
    (HERE/'upstream'/(name+'.lean')).write_bytes(src.read_bytes())
    records.append(dict(module=name,source_path=expected[name]['path'],source_sha256=sha(src),source_sha256_lf=lf(src),olean_path=str(obj),olean_sha256=sha(obj),inherited_log_path=str(log),inherited_log_sha256=sha(log)))
out=dict(status='SOURCE_HASHES_MATCH_PINNED_SUPPORT',receipt_path=str(receipt),receipt_sha256=sha(receipt),build=str(build),modules=records,scope='Five normalization modules reuse existing compiled support. Sources match the pinned support receipt and current maintained sources after line-ending normalization. The inherited dependency tree is not rebuilt.')
(HERE/'data/support.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(records),'modules',flush=True)
