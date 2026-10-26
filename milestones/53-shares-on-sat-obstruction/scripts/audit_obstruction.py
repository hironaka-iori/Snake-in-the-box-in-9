"""Reconstruct the saved count cycle, verify controls, and compute cyclic share packing."""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/52-share-on-235/scripts'))
from geometry_helpers import forest,shares
def canon(ds):
 d={};return tuple(d.setdefault(x,len(d)) for x in ds)
def key(ds,cs):return min((canon(ds),tuple(cs)),(canon(ds[::-1]),tuple(cs[::-1])))
source=json.loads((HERE/'data/upstream/obstruction_B6.json').read_text());edges=source['edges'];options=[]
for i,e in enumerate(edges):
 ds=e['dirs8'];assert canon(ds[1:])==canon(edges[(i+1)%16]['dirs8'][:7])
 k,cs,status=e['windows'][-1];assert len(cs)==6 and status=='SAT'
 opts=[a for a in {tuple(cs),tuple(cs[::-1])} if all(key(ds[-len(b)-1:],a[-len(b):])==(tuple(d),tuple(b)) for d,b,_ in e['windows'])]
 assert opts;options.append(opts)
solutions=[choice for choice in itertools.product(*options) if all(choice[i][1:]==choice[(i+1)%16][:-1] for i in range(16))]
assert len(solutions)==1;counts=solutions[0];mean=Fraction(sum(c[-1] for c in counts),16);assert mean==Fraction(65,16)
windows=json.loads((HERE/'data/windows.json').read_text());ids={key(r['directions'],r['counts']):i for i,r in enumerate(windows)}
phase_ids=[ids[key(e['dirs8'][-6:],counts[i][-5:])] for i,e in enumerate(edges)]
controls=[]
for i,row in enumerate(windows):
 p=HERE/f'data/controls/w{i:02d}.json';r=json.loads(p.read_text());assert r['status']=='SAT';W=[0]
 for d in row['directions']:W.append(W[-1]^(1<<d))
 S=set(r['selected']);a=forest(S,W);ss=shares(S,W[1:-1])
 assert a==r['census']['alpha'] and ss==r['census']['share'] and all(lo<=v<=hi for v,(lo,hi) in zip(a,r['bounds']))
 controls.append(dict(file=p.relative_to(HERE).as_posix(),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),share=sum(ss)))
screen=json.loads((HERE/'data/screen.json').read_text());proposed={i for i,r in enumerate(screen) if r['status']=='INFEASIBLE'}
def pack(allowed,forward_only=False):
 phases=[i for i,k in enumerate(phase_ids) if k in allowed and (not forward_only or (canon(edges[i]['dirs8'][-6:])==tuple(windows[k]['directions']) and tuple(counts[i][-5:])==tuple(windows[k]['counts'])))];best=[]
 for mask in range(1<<len(phases)):
  chosen=[i for j,i in enumerate(phases) if mask>>j&1];covered=[(i-j)%16 for i in chosen for j in range(5)]
  if len(covered)==len(set(covered)) and len(chosen)>len(best):best=chosen
 share=96*len(best)
 return dict(eligible_phases=phases,credited_phases=best,disjoint_cyclic_intervals=len(best),share_per_period=share,normalized_charge_mean=str(mean+Fraction(share,24*16)))
out=dict(status='PASS',count_mean=str(mean),counts=counts,phase_window_ids=phase_ids,controls=controls,single_candidate=pack({0}),selected_forward_pair=pack({0,5},True),all_numerical_candidates=pack(proposed),scope='Exact reconstruction and cyclic packing only. The local share premises need Lean checks; boundary corrections and coverage of other cycles are not supplied by this computation.')
(HERE/'data/obstruction-audit.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['counts','controls']})
