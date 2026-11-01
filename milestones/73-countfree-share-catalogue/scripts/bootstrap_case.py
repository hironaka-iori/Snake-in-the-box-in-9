"""Instantiate the audited count-free pipeline for one selected direction shape."""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
SOURCE=ROOT/'milestones/72-four-count-proof-closure/critical-current'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
index=int(sys.argv[1]);assert 0<=index<9
portfolio=read(SOURCE/'data/portfolio.json');case=portfolio['selected'][index]
assert portfolio['status']=='ALL_NINE_NATIVE_PREMISES_VERIFIED'
meta=read(SOURCE/'data'/case['certificate']);assert meta['status']=='NATIVE_DRAT_VERIFIED'
assert meta['cap']+1==case['required_share'] and meta['bounds']==[[0,21]]*5
number=7300+index;OUT=HERE/'cases'/f'case{number}';short=f'Share{number}';module=f'ShareWindow{number}';slug=f'share{number}'
for d in ['scripts','lean/'+short,'data','certificates','logs','build']:(OUT/d).mkdir(parents=True,exist_ok=True)
def write(path,text):path.write_text(text,encoding='utf-8',newline='\n')
def exact(s,a,b):
 assert a in s,a
 return s.replace(a,b)
def rename(s):
 return s.replace('ShareWindow12',module).replace('Share12',short).replace('share12',slug).replace('ckAllS_append_true12',f'ckAllS_append_true{number}')
tag=case['certificate'].removesuffix('-certificate.json');native=str(SOURCE/'data'/case['certificate']).replace('\\','/')
original=str(SOURCE/'build'/f'{tag}.cnf').replace('\\','/');core=str(SOURCE/'build'/f'{tag}.core.cnf').replace('\\','/')
for name in ['prepare_lean.py','replay_share.py','complete_share.py','audit_share.py']:
 s=rename((SOURCE/'scripts'/name).read_text())
 s=exact(s,"ROOT=HERE.parents[2];OUT=HERE/'share-proof'","ROOT=HERE.parents[3];OUT=HERE")
 if name in ['prepare_lean.py','audit_share.py']:
  s=exact(s,"HERE/'data/general8-cap11-certificate.json'",f"Path('{native}')")
  s=exact(s,"HERE/'build/general8-cap11.cnf'",f"Path('{original}')")
  if name=='prepare_lean.py':
   s=exact(s,"HERE/'build/general8-cap11.core.cnf'",f"Path('{core}')")
   s=exact(s,"prior={'cycle_cuts':[]}","prior={'cycle_cuts':meta.get('cycle_cuts',[])}")
   s=exact(s,"meta['bounds'],11)",f"meta['bounds'],{meta['cap']})")
   s=exact(s,'cap : Nat := 11',f"cap : Nat := {meta['cap']}")
  else:
   s=exact(s,"native['bounds'],11)",f"native['bounds'],{meta['cap']})")
   s=exact(s,'for cc in []:','for cc in native.get(\'cycle_cuts\',[]):')
   s=exact(s,'share_lower=12',f"share_lower={case['required_share']}")
 write(OUT/'scripts'/name,s)
s=rename((SOURCE/'scripts/assemble_countfree.py').read_text())
s=exact(s,"OUT=HERE/'share-proof'","OUT=HERE")
write(OUT/'scripts/assemble.py',s)
for name in ['Compose','Refuted']:
 write(OUT/f'lean/{short}/{name}.lean',rename((SOURCE/f'share-proof/lean/Share12/{name}.lean').read_text()))
write(OUT/'lean/LocalWindowShareBridge.lean',(SOURCE/'share-proof/lean/LocalWindowShareBridge.lean').read_text())
write(OUT/'data/bridge-source.json',(SOURCE/'share-proof/data/bridge-source.json').read_text())
ds=meta['directions'];names=list('abcdef')[:max(ds)+1]
u='['+','.join(names)+']';word='['+','.join(names[d] for d in ds)+']'
geometry=f'''import {short}.Refuted
import LocalWindowShareBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.{module}
set_option maxHeartbeats 0
theorem share_bound {{m : Nat}} (p : Snake m) (r {' '.join(names)} : Nat)
    (hn : {u}.Nodup) (h9 : ∀ x ∈ {u}, x < 9)
    (hr : r + 6 ≤ m)
    (hd : ∀ j, j < 6 → dir p (r+j) = ({word} : List Nat).getD j 0) :
    {case['required_share']} ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  have hs := mkPerm_spec hn h9 (by simp)
  have result := refuted_share_bridge p (mkPerm {u}) r refuted
    (cs := {ds}) ⟨rfl,rfl,by decide⟩ (by decide) hr
    (by
      intro j hj
      have hj6 : j < 6 := by simpa using hj
      rw [hd j hj6]
      interval_cases j
'''
geometry+=''.join(f'      · exact hs {d} (by simp)\n' for d in ds)
geometry+='''    )
    (by
      intro i hi
      have hi5 : i < 5 := by simpa [bounds] using hi
      have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
      interval_cases i <;> simpa [bounds] using hu)
  simpa [bounds, cap, resolution] using result
#print axioms share_bound
'''+f'end Snake9.LocalWindow.{module}\n'
write(OUT/f'lean/{short}/Geometry.lean',geometry)
record=dict(case_number=number,index=index,namespace=module,prefix=short,slug=slug,selected=case,native_metadata=meta,native_metadata_sha256=sha(Path(native)),source_checkpoint='c3bfc952a1a67191391ebc90c681f8fb6e897bb2',template_sha256={p.name:sha(p) for p in [SOURCE/'scripts'/n for n in ['prepare_lean.py','replay_share.py','complete_share.py','audit_share.py','assemble_countfree.py']]},scope='Generated proof attempt; no local theorem is claimed before semantic, replay, geometry and axiom gates pass.')
write(OUT/'data/case.json',json.dumps(record,indent=2)+'\n')
print(number,case['directions'],'share',case['required_share'],str(OUT))
