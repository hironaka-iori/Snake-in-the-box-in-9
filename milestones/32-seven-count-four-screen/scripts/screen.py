"""Attempt to falsify a direction-independent seven-count-four hypothesis.

All statuses are solver-only; a positive radius-four forest need not extend to
a complete snake. Results are saved immediately so an interrupted run resumes.
"""
import hashlib,itertools,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import window,plain,canonical
(HERE/'data').mkdir(parents=True,exist_ok=True)
shapes=[()]
for length in range(8):
    shapes=[d+(a,) for d in shapes for a in range(min(max(d,default=-1)+2,9))
            if len(set(w:=window(d+(a,))))==len(w) and
            all((w[i]^w[j]).bit_count()!=1 for i in range(len(w)) for j in range(i+2,len(w)))]
assert len(shapes)==132
(HERE/'data/shapes.json').write_text(json.dumps(shapes,indent=2)+'\n')
for i,ds in enumerate(shapes):
    p=HERE/f'data/window-{i:03d}.json'
    if p.exists():continue
    row=plain(dict(dirs=list(ds)),5);row['alpha']=[[4,4]]*7
    row['script_sha256_lf']=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
    p.write_text(json.dumps(row,indent=2)+'\n')
    print(i,''.join(map(str,ds)),row['status'],flush=True)
    if row['status']=='SAT':
        print('Local forest found: universal local-exclusion route is falsified.',flush=True)
        break
