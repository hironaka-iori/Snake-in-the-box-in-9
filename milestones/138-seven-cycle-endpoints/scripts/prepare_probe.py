"""Prepare exact necessary full-cube models for the selected seven-cycle row."""
from pathlib import Path
from itertools import combinations
import hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.dont_write_bytecode=True
sys.path[:0]=[str(R/'work/share_packages'),str(R/'work/solver_packages'),str(R/'milestones/10-window-aggregate/scripts')]
from gen_lean_sat import TaggedEncoding
from wincert import Encoding
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=R/'milestones/131-odd-pair-six-count/data/odd-pair9-six25/results.json'
j=json.loads(source.read_text())
profile=next(p for p in j['profiles'] if p['profile']=='conditional_floor18')
row=next(e for e in profile['cycle'] if e['edge']==992157)
directions=row['directions'];assert directions==[0,1,2,3,0,1,4,3,0]
assert row['counts']==[6,3,3,3,5,2]
window=[0]
for d in directions:window.append(window[-1]^(1<<d))
assert len(set(window))==len(window)
assert all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(window) for j,y in enumerate(window) if j>i)
bounds=[(0,21),(0,21)]+[(x,x) if x<6 else (6,21) for x in row['counts']]
for label in ['base','away']:
 folder=H/'work'/label;folder.mkdir(exist_ok=True)
 assert not any(folder.iterdir()),'Preserve existing input'
 enc=TaggedEncoding(window,bounds,radius=9)
 ref=Encoding(window,bounds,radius=9)
 assert enc.nv==ref.nv and enc.clauses==ref.clauses
 assert enc.ball==list(range(512)) and all(enc.meaning[513+v]==('e',v) for v in range(512))
 centres=window[3:9]
 forbidden=sorted({v for v in range(512) if any((v^c).bit_count()==2 for c in centres)}) if label=='away' else []
 for v in forbidden:enc.add([-(513+v)],('endpoint_away',v))
 raw=(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode('ascii')
 (folder/'base.cnf').write_bytes(raw)
 sources=[source,Path(__file__),H/'scripts/probe.py',R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',R/'milestones/10-window-aggregate/scripts/wincert.py']
 metadata=dict(status='PREPARED_NOT_RUN',label=label,edge=992157,source_profile='conditional_floor18',directions=directions,window=window,
  bounds=bounds,counted_offsets=list(range(3,9)),counts=row['counts'],symbol6_means='at least six',centres=centres,
  forbidden_endpoints=forbidden,variables=enc.nv,clauses=len(enc.clauses),cnf_sha256=hashlib.sha256(raw).hexdigest(),
  variable_meaning=enc.meaning,counters=enc.ctrs,source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in sources},
  scope='Necessary full-cube degree, endpoint, count and cycle constraints only. Base has no endpoint location restriction. Away forbids distance two from all six counted centres. SAT must be checked as one actual induced path; native UNSAT needs a checked certificate.')
 (folder/'encoding.json').write_text(json.dumps(metadata,indent=2)+'\n',encoding='utf-8')
 print(json.dumps({k:metadata[k] for k in ['label','window','bounds','variables','clauses','forbidden_endpoints']}))
