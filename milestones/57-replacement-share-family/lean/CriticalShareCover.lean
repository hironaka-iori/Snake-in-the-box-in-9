import Mathlib.Tactic
namespace Snake9.CriticalShareCover57

def edges : List (Nat × Nat × Nat) := [(0,11,1),(1,12,13),(2,10,13),(3,19,2),(4,18,12),(5,27,14),(6,28,6),(7,29,6),(8,14,0),(9,13,12),(9,15,14),(11,22,11),(11,17,5),(10,20,9),(12,21,10),(11,24,5),(13,30,7),(14,32,15),(14,33,16),(15,35,8),(16,7,3),(17,5,8),(18,6,4),(19,2,10),(20,1,9),(21,0,2),(22,4,7),(23,3,1),(22,4,7),(23,3,1),(24,5,8),(25,7,3),(26,31,1),(26,34,1),(27,36,4),(28,8,3),(29,9,4),(28,8,3),(29,9,4),(31,19,2),(30,23,11),(32,16,0),(32,16,0),(33,25,0),(34,19,2),(33,25,0),(35,26,5),(36,28,6)]
def rank (v : Nat) : Nat := ([8, 5, 2, 0, 2, 2, 4, 10, 6, 12, 3, 0, 6, 13, 7, 13, 9, 1, 3, 1, 4, 7, 1, 15, 1, 9, 15, 3, 5, 11, 14, 0, 8, 8, 0, 14, 4] : List Nat).getD v 0

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
