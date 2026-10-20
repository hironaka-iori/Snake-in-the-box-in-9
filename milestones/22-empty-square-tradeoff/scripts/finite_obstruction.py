"""Check a 238-edge abstract sequence surviving the frozen masks and length-nine geometry."""
import hashlib,json,pathlib
from research import canon, induced, window_key
P=pathlib.Path(__file__).resolve().parents[1];R=P.parents[1]
src=P/'runs/value-gate.json';cycle=json.loads(src.read_text())['experiments'][-1]['cycle']
assert cycle[0]['count']==6
ds=list(cycle[0]['shape'])
for t in range(238-len(ds)):
    e=cycle[t%len(cycle)]
    assert list(canon(ds[-8:]))==e['shape']
    labels=list(dict.fromkeys(ds[-8:]))
    assert e['append_label']<len(labels)
    ds.append(labels[e['append_label']])
alpha=[4]+[1 if i%2 else 6 for i in range(1,238)]+[4]
index=R/'milestones/10-window-aggregate/data/direction_certificates_k5p.json'
forb={(tuple(x['dirs']),tuple(map(tuple,x['alpha']))) for x in json.loads(index.read_text())['cases']}
assert all(induced(ds[j:j+9]) for j in range(len(ds)-8))
for k in range(2,6):
    for j in range(239-k-1):
        assert window_key(ds[j:j+k+1],alpha[j+1:j+k+1]) not in forb
T=sum(alpha); E=18428-70*239-2*T
assert (T,E)==(835,28) and E%4==0
vertices=[0]
for d in ds:vertices.append(vertices[-1]^(1<<d))
assert len(set(vertices))<len(vertices)
out={'status':'ABSTRACT_OBSTRUCTION','v':239,'m':238,'T':T,'E':E,
     'minimum_empty_squares_needed_to_exclude_238_with_current_potential':18,
     'directions':ds,'alpha':alpha,'global_distinctness':False,
     'length9_direction_windows_induced':True,'frozen175_masks_avoided':True,
     'input_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
     'script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
     'model_code_sha256':hashlib.sha256((P/'scripts/research.py').read_bytes()).hexdigest(),
     'index_sha256':hashlib.sha256(index.read_bytes()).hexdigest(),
     'meaning':'No actual snake or empty-face realization is asserted; added constraints alone cannot exclude m=238.'}
(P/'runs/finite-obstruction.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: abstract m=238, T=835, E=28; globally repeats vertices.')
