from pathlib import Path
import hashlib,importlib.util,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
np=model.np
records=json.loads((HERE/'data/forced-geometry.json').read_text())['patterns']
spec=importlib.util.spec_from_file_location('analyze58',ROOT/'milestones/54-share-coverage/scripts/analyze.py')
analyze=importlib.util.module_from_spec(spec);spec.loader.exec_module(analyze);analyze.HERE=HERE
for source,name in [(ROOT/'milestones/57-replacement-share-family/combined','geometry'),(HERE/'candidate','geometry-candidate')]:
    meta=json.loads((source/'data/model.json').read_text())
    with np.load(source/'build/graph.npz') as z:a={k:z[k] for k in z.files}
    for k,h in meta['arrays_sha256'].items():assert hashlib.sha256(a[k].tobytes()).hexdigest()==h
    assert [r['directions'] for r in records]==meta['extensions']
    lookup=np.array([r['share_lower'] for r in records],dtype=a['share_lower'].dtype)
    old=a['share_lower'].copy();a['share_lower']=np.maximum(old,lookup[a['direction']])
    dest=HERE/name;(dest/'data').mkdir(parents=True,exist_ok=True);(dest/'build').mkdir(exist_ok=True)
    np.savez_compressed(dest/'build/graph.npz',**a)
    meta['arrays_sha256']={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in a.items()}
    meta['forced_geometric_credits']=[r['share_lower'] for r in records]
    meta['geometric_certificate']='data/forced-geometry.json'
    meta['source']=source.relative_to(ROOT).as_posix()
    meta['strengthened_transitions']=int((a['share_lower']>old).sum())
    meta['scope']='Finite model with explicit forced-absence credits. Lean status is recorded separately in data/lean-audit.json; inherited numerical premises remain.'
    (dest/'data/model.json').write_text(json.dumps(meta,indent=2)+'\n')
    analyze.run(name,True)
