"""Recheck the exact mean certificate and an unsaturated attaining cycle."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
hashraw=lambda b:hashlib.sha256(b).hexdigest()
for name in ['data','lean','logs','build']:(HERE/name).mkdir(parents=True,exist_ok=True)
old=ROOT/'milestones/73-countfree-share-catalogue'
source=ROOT/'milestones/72-four-count-proof-closure/critical-current'
model_path=old/'data/proved-model.json';model=read(model_path)
assert model['status']=='EXACT_PROOF_SUPPORTED_LOCAL_MODEL' and not model['additional_share_assumptions']
assert model['mean']=='483' and model['potential_range']==551
for rel,digest in model['audited_local_sources'].items():assert sha(ROOT/rel)==digest
extension_path=ROOT/'milestones/59-extended-share-window/extended/data/model.json'
extensions=read(extension_path)['extensions']
start=time.monotonic()
with np.load(source/'build/source-graph.npz') as z:arrays={k:z[k] for k in z.files}
for k,digest in model['source_arrays_sha256'].items():assert hashraw(arrays[k].tobytes())==digest
def canon(word):
    d={};return tuple(d.setdefault(x,len(d)) for x in word)
floors={tuple(r['shape']):r['share'] for r in model['countfree_floors']}
W=arrays['weight'].astype(np.int64).copy()
for di,ds in enumerate(extensions):
    shape=min(canon(ds[-6:]),canon(ds[-6:][::-1]))
    if shape in floors:
        ix=arrays['direction']==di
        W[ix]=np.maximum(W[ix],120*(arrays['count_code'][ix]%6+1)+floors[shape])
assert hashraw(W.tobytes())==model['weight_sha256']
potential_path=old/'data/proved-potential.i64.gz'
raw=gzip.decompress(potential_path.read_bytes());assert hashraw(raw)==model['potential_sha256']
pi=np.frombuffer(raw,dtype='<i8');U=arrays['U'];V=arrays['V']
assert len(pi)==model['states'] and len(U)==model['edges']==4947008
assert np.all(483+pi[V]<=W+pi[U]) and int(pi.max()-pi.min())==551
cycle=[]
for saved in model['cycle']:
    i=saved['edge'];code=int(arrays['count_code'][i]);di=int(arrays['direction'][i])
    assert (int(U[i]),int(V[i]),int(W[i]))==(saved['u'],saved['v'],saved['weight'])
    counts=[code//6**j%6+1 for j in range(5,-1,-1)]
    assert all(1<=c<6 for c in counts)
    cycle.append(dict(saved,direction_id=di,directions=extensions[di],count_code=code,counts=counts,
                      history=int(arrays['history'][i])))
assert len(cycle)==4 and sum(x['weight'] for x in cycle)==1932
assert [x['weight'] for x in cycle]==[252,480,600,600]
assert all(x['v']==cycle[(i+1)%4]['u'] for i,x in enumerate(cycle))
threshold=Fraction(111960,227);ideal=Fraction(1098960+8*483,4200+483)
assert 227*483<111960 and ideal>235
inputs=[Path(__file__),model_path,potential_path,extension_path,source/'data/source-proved-model.json']
out=dict(status='PASS_UNSATURATED_ATTAINING_CYCLE',cycle=cycle,states=len(pi),edges=len(U),
    mean=483,weight_sha256=hashraw(W.tobytes()),potential_sha256=hashraw(raw),potential_range=551,
    all_edge_inequalities_checked=True,all_cycle_digits_below_six=True,
    strict_mean_threshold_for_234=str(threshold),zero_range_comparison=str(ideal),
    threshold_deficit_at_mean483=111960-227*483,
    source_sha256={p.relative_to(ROOT).as_posix():sha(p) for p in inputs},
    source_arrays_sha256=model['source_arrays_sha256'],seconds=time.monotonic()-start,
    scope='Exact finite graph. Every nonnegative bonus that vanishes when all six symbols are below six preserves its minimum mean 483. With the same budget, no slope and nonnegative potential range can exclude 235. Actual snake realization of this cycle is unproved.')
(HERE/'data/graph-audit.json').write_text(json.dumps(out,indent=2)+'\n')
literal='['+','.join('['+','.join(map(str,r['counts']))+']' for r in cycle)+']'
src='''import Mathlib.Tactic
namespace Snake9.UnsaturatedObstruction82

def cycleCounts : List (List Nat) := COUNTS

theorem cycle_counts_below_six :
    ∀ row ∈ cycleCounts, ∀ c ∈ row, c < 6 := by decide

theorem cycle_weight_sum : (252+480+600+600 : Nat) = 4*483 := by decide

theorem cycle_slope (p d x0 x1 x2 x3 : ℚ)
    (h0 : p+x1 ≤ 252*d+x0) (h1 : p+x2 ≤ 480*d+x1)
    (h2 : p+x3 ≤ 600*d+x2) (h3 : p+x0 ≤ 600*d+x3) :
    p ≤ 483*d := by linarith

theorem no_234_criterion (p d R : ℚ) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hp : p ≤ 483*d) : ¬ 111960*d+R < 227*p := by linarith

theorem cycle_prevents_234 (p d R x0 x1 x2 x3 : ℚ)
    (hd : 0 ≤ d) (hR : 0 ≤ R)
    (h0 : p+x1 ≤ 252*d+x0) (h1 : p+x2 ≤ 480*d+x1)
    (h2 : p+x3 ≤ 600*d+x2) (h3 : p+x0 ≤ 600*d+x3) :
    ¬ 111960*d+R < 227*p :=
  no_234_criterion p d R hd hR (cycle_slope p d x0 x1 x2 x3 h0 h1 h2 h3)

theorem nonnegative_bonus_preserves_potential (p d w bonus u v : ℚ)
    (hd : 0 ≤ d) (hb : 0 ≤ bonus) (h : p+v ≤ d*w+u) :
    p+v ≤ d*(w+bonus)+u := by nlinarith

#print axioms cycle_counts_below_six
#print axioms cycle_weight_sum
#print axioms cycle_slope
#print axioms no_234_criterion
#print axioms cycle_prevents_234
#print axioms nonnegative_bonus_preserves_potential
end Snake9.UnsaturatedObstruction82
'''.replace('COUNTS',literal)
(HERE/'lean/UnsaturatedCycle.lean').write_text(src,encoding='utf-8',newline='\n')
print(out['status'],'mean',483,'zero-range comparison',ideal,'deficit',out['threshold_deficit_at_mean483'])
