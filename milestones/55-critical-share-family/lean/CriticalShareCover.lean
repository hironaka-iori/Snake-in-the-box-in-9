import Mathlib.Tactic
namespace Snake9.CriticalShareCover55

def edges : List (Nat × Nat × Nat) := [(1,18,16),(1,19,18),(0,25,12),(3,34,20),(2,30,11),(2,38,11),(4,44,14),(5,45,22),(7,47,14),(6,50,20),(8,26,11),(9,27,13),(11,28,1),(8,21,19),(10,23,17),(12,20,6),(13,24,15),(14,20,6),(15,22,2),(16,36,10),(17,31,12),(17,32,13),(17,39,12),(17,40,13),(20,49,9),(18,41,21),(19,42,22),(21,43,23),(22,44,14),(23,46,23),(24,48,21),(25,52,0),(26,51,7),(27,52,0),(28,53,24),(25,55,0),(26,54,7),(27,55,0),(28,56,25),(29,5,4),(30,4,2),(31,6,5),(32,7,3),(33,1,6),(34,0,5),(33,1,6),(34,0,5),(35,3,8),(36,2,7),(35,3,8),(36,2,7),(37,5,4),(38,4,2),(39,6,5),(40,7,3),(41,10,15),(42,11,4),(43,13,17),(44,9,3),(45,14,18),(46,15,19),(47,8,2),(48,12,16),(41,10,15),(42,11,4),(43,13,17),(44,9,3),(45,14,18),(46,15,19),(47,8,2),(48,12,16),(49,17,0),(50,16,8),(49,17,0),(50,16,8),(52,33,9),(51,35,10),(53,29,1),(53,29,1),(56,37,1),(55,33,9),(54,35,10),(56,37,1)]
def rank (v : Nat) : Nat := ([12, 0, 8, 10, 10, 7, 4, 4, 6, 12, 3, 3, 12, 9, 9, 6, 6, 2, 1, 1, 0, 7, 7, 4, 10, 13, 7, 13, 4, 6, 9, 3, 3, 15, 11, 9, 7, 6, 9, 3, 3, 2, 2, 8, 11, 8, 5, 5, 11, 1, 5, 8, 14, 5, 8, 14, 5] : List Nat).getD v 0

theorem rank_certificate : edges.all (fun e => decide (e.2.2=6 ∨ rank e.1 < rank e.2.1)) = true := by decide

theorem uncovered_edge_increases (u v w : Nat) (he : (u,v,w) ∈ edges) (hw : w≠6) :
    rank u < rank v := by
  have h := List.all_eq_true.mp rank_certificate (u,v,w) he
  have h' : w=6 ∨ rank u < rank v := of_decide_eq_true h
  exact h'.resolve_left hw

theorem walk_increases (f w : Nat → Nat) (n : Nat)
    (he : ∀ i, i<n → (f i,f (i+1),w i) ∈ edges)
    (hw : ∀ i, i<n → w i≠6) : rank (f 0)+n ≤ rank (f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := ih (fun i hi => he i (by omega)) (fun i hi => hw i (by omega))
    have hstep := uncovered_edge_increases (f n) (f (n+1)) (w n) (he n (by omega)) (hw n (by omega))
    omega

theorem closed_walk_hits (f w : Nat → Nat) (n : Nat) (hn : 0<n)
    (hc : f n=f 0) (he : ∀ i, i<n → (f i,f (i+1),w i) ∈ edges) :
    ∃ i, i<n ∧ w i=6 := by
  by_contra! h
  have hsum := walk_increases f w n he h
  rw [hc] at hsum
  omega

#print axioms rank_certificate
#print axioms uncovered_edge_increases
#print axioms walk_increases
#print axioms closed_walk_hits
end Snake9.CriticalShareCover55
