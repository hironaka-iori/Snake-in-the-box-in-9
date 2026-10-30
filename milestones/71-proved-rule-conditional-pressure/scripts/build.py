"""Apply the numerical count basis to the proof-supported round-70 graph.

The numerical exclusions remain assumptions. Recovered proved rules are already
present in the input; no new numerical share rule is introduced.
"""
from pathlib import Path
import collections, gzip, hashlib, json, sys, time
HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
for name in ['build','data','logs','lean']:(HERE/name).mkdir(parents=True,exist_ok=True)
start=time.monotonic(); prior=ROOT/'milestones/70-proof-supported-share-model'
meta=read(prior/'data/enriched-model.json')
with np.load(prior/'build/enriched-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h
sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')
basis=json.loads(gzip.decompress((ROOT/'milestones/68-proof-dependency-pressure/data/count-subsumption.json.gz').read_bytes()))['needed']
def canon(w):
    names=list(dict.fromkeys(w));return tuple(names.index(x) for x in w)
def encode(c):
    n=0
    for x in c:n=6*n+x-1
    return n
table=collections.defaultdict(set)
for w,c in basis:
    table[canon(w)].add(encode(c));table[canon(w[::-1])].add(encode(c[::-1]))
keep=np.ones(len(a['U']),dtype=bool)
for di,ds in enumerate(sm['extensions']):
    ix=np.flatnonzero(a['direction']==di);code=a['count_code'][ix];reject=np.zeros(len(ix),dtype=bool)
    for offset in range(5):
        for width in range(2,7-offset):
            word=canon(ds[2+offset:3+offset+width])
            if word in table:reject|=np.isin(code//6**(6-offset-width)%6**width,list(table[word]))
    keep[ix]=~reject
out={k:v[keep] for k,v in a.items()}
np.savez_compressed(HERE/'build/graph.npz',**out)
report=dict(states=meta['states'],edges=len(out['U']),candidate_edges=len(keep),additional_basis_keys=len(basis),arrays_sha256={k:sha(v.tobytes()) for k,v in out.items()},source_arrays_sha256=meta['arrays_sha256'],seconds=time.monotonic()-start,scope='Conditional finite model; all additional count basis keys assumed forbidden. No global upper-bound claim.')
(HERE/'data/model.json').write_text(json.dumps(report,indent=2)+'\n');print(report,flush=True)
