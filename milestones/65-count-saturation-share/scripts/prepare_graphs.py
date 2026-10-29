from pathlib import Path
from fractions import Fraction
import collections,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
share=next(g for g in json.loads((HERE/'data/candidate-analyses.json').read_text()) if g['mode']=='shares_only')
mu=Fraction(share['integer_mean']);p,d=mu.numerator,mu.denominator
es=[(e['u'],e['v'],e['weight']) for e in share['edges']];cy=[es[i] for i in share['cycle']]
src=f'''import FinitePotential
namespace Snake9.CriticalFamily61.CountShare65
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def edges : List (Nat × Nat × Nat) := {es}
def potential : List Nat := {share['potential']}
def cycle : List (Nat × Nat × Nat) := {cy}
theorem checked : checkEdges {p} {d} potential edges=true := by decide +kernel
theorem every_closed_walk (n : Nat) (f w : Nat → Nat)
    (h : ∀ i<n, (f i,f (i+1),w i)∈edges) (hc : f n=f 0) :
    n*{p}≤{d}*(∑ i∈Finset.range n,w i) := by
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
end Snake9.CriticalFamily61.CountShare65
'''
(HERE/'lean/SharePotential.lean').write_text(src,encoding='utf-8')
old=json.loads((ROOT/'milestones/64-neighbour-choice-share/data/analysis.json').read_text());N=old['states']
edges=[(e['u'],e['v']) for i,e in enumerate(old['edges']) if i!=24]
degree=collections.Counter(v for u,v in edges);out=collections.defaultdict(list)
for i,(u,v) in enumerate(edges):out[u].append((v,i))
queue=collections.deque(v for v in range(N) if degree[v]==0);rank=[0]*N;pred={};visited=[]
while queue:
    u=queue.popleft();visited.append(u)
    for v,i in out[u]:
        if rank[u]+1>rank[v]:rank[v]=rank[u]+1;pred[v]=(u,i)
        degree[v]-=1
        if degree[v]==0:queue.append(v)
assert len(visited)==N and all(rank[u]<rank[v] for u,v in edges)
R=max(rank);v=rank.index(R);walk=[v]
while v in pred:v,_=pred[v];walk.append(v)
walk.reverse();assert len(walk)==R+1
data=dict(states=N,excluded_edge=24,edges=edges,rank=rank,maximum_length=R,attaining_walk=walk,
    scope='Finite graph after removal of transition 24; no assertion that all snake windows belong to this restricted family.')
(HERE/'data/acyclic-family.json').write_text(json.dumps(data,indent=2)+'\n')
src=f'''import Mathlib.Tactic
namespace Snake9.CountDAG65
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def edges : List (Nat × Nat) := {edges}
def rank : List Nat := {rank}
def walk : List Nat := {walk}
theorem checked : edges.all (fun e => decide (rank.getD e.1 0+1≤rank.getD e.2 0))=true := by decide +kernel
theorem rank_bound : ∀ v : Fin {N}, rank.getD v.val 0≤{R} := by decide +kernel
theorem path_rank (rho f : Nat → Nat) : ∀ n,
    (∀ i<n, rho (f i)+1≤rho (f (i+1))) → rho (f 0)+n≤rho (f n) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    have hp := ih (by intro i hi; exact h i (by omega))
    have hl := h n (by omega)
    omega
theorem every_walk (n : Nat) (f : Nat → Fin {N})
    (h : ∀ i<n, ((f i).val,(f (i+1)).val)∈edges) : n≤{R} := by
  have hp := path_rank (fun v => rank.getD v 0) (fun i => (f i).val) n (by
    intro i hi
    exact of_decide_eq_true (List.all_eq_true.mp checked _ (h i hi)))
  have hb := rank_bound (f n)
  change rank.getD (f 0).val 0+n≤rank.getD (f n).val 0 at hp
  omega
theorem no_positive_closed_walk (n : Nat) (f : Nat → Nat) (hn : 0<n)
    (h : ∀ i<n, (f i,f (i+1))∈edges) (hc : f n=f 0) : False := by
  have hp := path_rank (fun v => rank.getD v 0) f n (by
    intro i hi
    exact of_decide_eq_true (List.all_eq_true.mp checked _ (h i hi)))
  rw [hc] at hp
  omega
theorem attained : walk.length={R+1} ∧
    (List.range {R}).all (fun i => edges.contains (walk.getD i 0,walk.getD (i+1) 0))=true := by decide +kernel
#print axioms checked
#print axioms rank_bound
#print axioms path_rank
#print axioms every_walk
#print axioms no_positive_closed_walk
#print axioms attained
end Snake9.CountDAG65
'''
(HERE/'lean/FamilyDAG.lean').write_text(src,encoding='utf-8')
print('Restricted share-only mean',mu/120,'DAG maximum walk length',R)
