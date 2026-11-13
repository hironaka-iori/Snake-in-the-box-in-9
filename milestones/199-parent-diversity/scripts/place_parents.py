from pathlib import Path
import argparse,hashlib,json,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--parents',required=True);ap.add_argument('--tag',required=True);a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=H/'data'/(a.parents+'.json');raw=source.read_bytes();parents=json.loads(raw)['parents']
catalogue=R/'milestones/197-symmetry-placement/data/placements-all.json';cases=json.loads(catalogue.read_bytes())['rows']
order=sorted(range(len(cases)),key=lambda i:(not(cases[i]['transpositions']==2 and cases[i]['flipped_fixed']==2),i))
maps=[]
for i in order:
 c=cases[i];maps.append((i,[sum(((v>>j)&1)<<c['permutation'][j] for j in range(7))^c['translation'] for v in range(128)]))
start=time.monotonic();rows=[];witness=None;samples=[];status='COMPLETE'
for parent_id,parent in enumerate(parents):
 p=parent['vertices'];mask=sum(1<<v for v in p);examined=0
 for case_id,values in maps:
  examined+=1
  if any((mask>>values[v])&1 for v in p):continue
  paths=[p,[128+values[v] for v in p]]
  assert len(set(paths[0]+paths[1]))==2*len(p) and all((u^v).bit_count()!=1 for u in paths[0] for v in paths[1])
  for q in paths:assert all(((v^q[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(q) for j in range(i+1,len(q)))
  witness=dict(parent=parent_id,matching=case_id,case=cases[case_id],paths=paths,fixed_face_vertices=2*len(p));status='WITNESS';break
 rows.append(dict(parent=parent_id,examined=examined,separated=witness is not None))
 if witness:break
 if parent_id%16==0:
  snap=snapshot();samples.append(snap)
  if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:status='RESOURCE_LIMIT';break
out=dict(status=status,seconds=time.monotonic()-start,parent_count=len(parents),matching_count=len(cases),rows=rows,witness=witness,resource_gate=gate,resource_samples=samples,source_sha256=hashlib.sha256(raw).hexdigest(),catalogue_sha256=hashlib.sha256(catalogue.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Each listed Q7 parent is placed against all6512 affine involutions unless a witness or resource stop is found. Separation is exactly S intersect h(S)=empty. This does not cover all near-optimal Q7 snakes.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(status=status,parents=len(rows),seconds=out['seconds'],witness=witness and {k:witness[k] for k in ['parent','matching','fixed_face_vertices']})),flush=True)
