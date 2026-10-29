from pathlib import Path
from fractions import Fraction
import json
HERE=Path(__file__).resolve().parents[1]
g=json.loads((HERE/'data/analysis.json').read_text());mu=Fraction(g['integer_mean']);p,d=mu.numerator,mu.denominator
triples=[(e['u'],e['v'],e['weight']) for e in g['edges']];cycle=[triples[i] for i in g['cycle']]
src=f'''import FinitePotential
namespace Snake9.CriticalFamily61.NeighbourChoice64
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
theorem below_234_threshold : (1991 : Rat)/4 < 112440/225 := by norm_num
theorem exact_threshold_gap : (112440 : Rat)/225-1991/4=119/60 := by norm_num
#print axioms checked
#print axioms every_closed_walk
#print axioms attaining_cycle
#print axioms attainment
#print axioms below_234_threshold
#print axioms exact_threshold_gap
end Snake9.CriticalFamily61.NeighbourChoice64
'''
(HERE/'lean/Potential.lean').write_text(src,encoding='utf-8')
