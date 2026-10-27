"""Generate a small rank certificate that every recorded critical cycle meets rule 1."""
from pathlib import Path
import collections,json
HERE=Path(__file__).resolve().parents[1]
edges=json.loads((HERE/'data/critical-edges.json').read_text())
cover=json.loads((HERE/'data/selected-candidate.json').read_text())
assert cover['selected']==[1]
nodes=sorted({e['u'] for e in edges}|{e['v'] for e in edges});index={v:i for i,v in enumerate(nodes)}
adj=collections.defaultdict(list);degree=collections.Counter();rank={v:0 for v in nodes}
for e in edges:
    if e['window']!=1:adj[e['u']].append(e['v']);degree[e['v']]+=1
queue=collections.deque(v for v in nodes if degree[v]==0);seen=[]
while queue:
    u=queue.popleft();seen.append(u)
    for v in adj[u]:
        rank[v]=max(rank[v],rank[u]+1);degree[v]-=1
        if degree[v]==0:queue.append(v)
assert len(seen)==len(nodes)
triples=[(index[e['u']],index[e['v']],e['window']) for e in edges]
source='''import Mathlib.Tactic
namespace Snake9.CriticalShareCover57

def edges : List (Nat × Nat × Nat) := EDGES
def rank (v : Nat) : Nat := RANKS.getD v 0

theorem rank_certificate : edges.all (fun e => decide (e.2.2=1 ∨ rank e.1 < rank e.2.1)) = true := by decide

theorem uncovered_edge_increases (u v w : Nat) (he : (u,v,w) ∈ edges) (hw : w≠1) :
    rank u < rank v := by
  have h := List.all_eq_true.mp rank_certificate (u,v,w) he
  have h' : w=1 ∨ rank u < rank v := of_decide_eq_true h
  exact h'.resolve_left hw

theorem walk_increases (f w : Nat → Nat) (n : Nat)
    (he : ∀ i, i<n → (f i,f (i+1),w i) ∈ edges)
    (hw : ∀ i, i<n → w i≠1) : rank (f 0)+n ≤ rank (f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := ih (fun i hi => he i (by omega)) (fun i hi => hw i (by omega))
    have hstep := uncovered_edge_increases (f n) (f (n+1)) (w n) (he n (by omega)) (hw n (by omega))
    omega

theorem closed_walk_hits (f w : Nat → Nat) (n : Nat) (hn : 0<n)
    (hc : f n=f 0) (he : ∀ i, i<n → (f i,f (i+1),w i) ∈ edges) :
    ∃ i, i<n ∧ w i=1 := by
  by_contra! h
  have hsum := walk_increases f w n he h
  rw [hc] at hsum
  omega

#print axioms rank_certificate
#print axioms uncovered_edge_increases
#print axioms walk_increases
#print axioms closed_walk_hits
end Snake9.CriticalShareCover57
'''
source=source.replace('EDGES','['+','.join(f'({u},{v},{w})' for u,v,w in triples)+']')
source=source.replace('RANKS','('+str([rank[v] for v in nodes])+' : List Nat)')
(HERE/'lean').mkdir(exist_ok=True);(HERE/'lean/CriticalShareCover.lean').write_text(source,encoding='utf-8')
(HERE/'data/rank-certificate.json').write_text(json.dumps(dict(original_nodes=nodes,ranks=[rank[v] for v in nodes],
    edges=triples,selected_window=1,scope='Rank certificate for the recorded 48-edge critical graph only.'),indent=2)+'\n')
