from pathlib import Path
import json
from fractions import Fraction
HERE=Path(__file__).resolve().parents[1]
rows=json.loads((HERE/'data/split-share.json').read_text())['rows']
for r in rows:
    if r['lower']<=r['old']:continue
    i=r['edge'];q=r['split'];D0=[x for x in r['absent0'] if x!=q]
    src=f'''import SplitShare
namespace Snake9.LocalWindow.SplitShare62.E{i:02d}
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := {r['vertices']}
def ds : List Nat := {r['directions']}
def C : List Nat := {r['centres']}
def D0 : List Nat := {D0}
def D1 : List Nat := {r['absent1']}
def mask0 : Nat := {sum(1<<x for x in r['absent0'])}
def mask1 : Nat := {sum(1<<x for x in r['absent1'])}
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus ({q}::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 ({q}::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : {r['lower']} ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : {r['lower']} ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    {r['lower']} ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:={q}) (mask0:=mask0) (mask1:=mask1) (L:={r['lower']}) (start:=4)
    canonical (by decide) (by decide) rfl forced0 forced1 supported
    checked_mask0 checked_mask1 credit0 credit1 p P r hr hP
'''
    src+='\n'.join('#print axioms '+n for n in ['canonical','forced0','forced1','supported','checked_mask0','checked_mask1','credit0','credit1','in_snake'])
    src+=f'\nend Snake9.LocalWindow.SplitShare62.E{i:02d}\n'
    (HERE/f'lean/Edge{i:02d}.lean').write_text(src,encoding='utf-8')
print('Prepared',sum(r['lower']>r['old'] for r in rows),'geometric improvements')
for g in json.loads((HERE/'data/graph-analyses.json').read_text()):
    n=g['length'];mu=Fraction(g['integer_mean']);p,d=mu.numerator,mu.denominator
    triples=[(e['u'],e['v'],e['weight']) for e in g['edges']];cycle=[triples[i] for i in g['cycle']]
    src=f'''import FinitePotential
namespace Snake9.CriticalFamily61.Split62Potential{n}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def edges : List (Nat × Nat × Nat) := {triples}
def potential : List Nat := {g['potential']}
def cycle : List (Nat × Nat × Nat) := {cycle}
theorem checked : checkEdges {p} {d} potential edges=true := by decide +kernel
theorem every_closed_walk (n : Nat) (f w : Nat → Nat)
    (h : ∀ i<n, (f i,f (i+1),w i)∈edges) (hc : f n=f 0) :
    n*{p} ≤ {d}*(∑ i ∈ Finset.range n, w i) := by
  apply closed_bound {p} {d} n (fun x => potential.getD x 0) f w ?_ hc
  intro i hi
  exact edge_of_check checked (h i hi)
theorem attaining_cycle : (List.range cycle.length).all (fun i =>
    edges.contains (cycle.getD i (0,0,0)) &&
    decide ((cycle.getD i (0,0,0)).2.1=(cycle.getD ((i+1)%cycle.length) (0,0,0)).1))=true := by decide +kernel
theorem attainment : {d}*(cycle.map (fun e => e.2.2)).sum={p}*cycle.length := by decide +kernel
#print axioms checked
#print axioms every_closed_walk
#print axioms attaining_cycle
#print axioms attainment
end Snake9.CriticalFamily61.Split62Potential{n}
'''
    (HERE/f'lean/Potential{n}.lean').write_text(src,encoding='utf-8')
