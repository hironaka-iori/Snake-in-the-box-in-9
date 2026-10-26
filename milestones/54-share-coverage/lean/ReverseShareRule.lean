import ShareFrame
import LocalWindowDirBridge
import Mathlib.Tactic

namespace Snake9.LocalWindow.ReverseShareRule

theorem share_rev {m : Nat} (M : Nat) (p : Snake m) {k : Nat} (hk : k ≤ m) :
    coreShare M (revSnake p) k = coreShare M p (m-k) := by
  unfold coreShare
  rw [sel_rev, vx_rev p hk]

theorem five_sum_rev {m : Nat} (M : Nat) (p : Snake m) (r : Nat) (hr : r+6 ≤ m) :
    ((List.range 5).map fun i => coreShare M (revSnake p) (m-r-6+i+1)).sum =
      ((List.range 5).map fun i => coreShare M p (r+i+1)).sum := by
  have h : ∀ i, i<5 → coreShare M (revSnake p) (m-r-6+i+1) = coreShare M p (r+5-i) := by
    intro i hi
    rw [share_rev M p (by omega)]
    congr 1
    omega
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 4 (by omega)
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil] at *
  rw [h0,h1,h2,h3,h4]
  simp only [Nat.add_zero]
  have e1 : r+5-1=r+4 := by omega
  have e2 : r+5-2=r+3 := by omega
  have e3 : r+5-3=r+2 := by omega
  have e4 : r+5-4=r+1 := by omega
  rw [e1,e2,e3,e4]
  norm_num only [Nat.sub_zero, Nat.add_assoc]
  omega

/-- Transfer any five-centre rule to a window read in the opposite direction. -/
theorem reverse_rule (ds : List Nat) (bounds : List (Nat × Nat)) (K : Nat)
    (hlocal : ∀ {n : Nat} (q : Snake n) (P : CPerm) (t : Nat), t+6≤n →
      (∀ j, j<6 → P.fwd (dir q (t+j)) = ds.getD j 0) →
      (∀ i, i<5 → (bounds.getD i (0,21)).1 ≤ coreAlpha q (t+i+1) ∧
        coreAlpha q (t+i+1) ≤ (bounds.getD i (0,21)).2) →
      K ≤ ((List.range 5).map fun i => coreShare 12 q (t+i+1)).sum)
    {m : Nat} (p : Snake m) (P : CPerm) (r : Nat) (hr : r+6≤m)
    (hd : ∀ j, j<6 → P.fwd (dir p (r+5-j)) = ds.getD j 0)
    (hb : ∀ i, i<5 → (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+5-i) ∧
      coreAlpha p (r+5-i) ≤ (bounds.getD i (0,21)).2) :
    K ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  have hdir : ∀ j, j<6 → P.fwd (dir (revSnake p) (m-r-6+j)) = ds.getD j 0 := by
    intro j hj
    rw [dir_rev p (by omega)]
    have e : m-(m-r-6+j)-1=r+5-j := by omega
    simpa only [e] using hd j hj
  have hcounts : ∀ i, i<5 → (bounds.getD i (0,21)).1 ≤ coreAlpha (revSnake p) (m-r-6+i+1) ∧
      coreAlpha (revSnake p) (m-r-6+i+1) ≤ (bounds.getD i (0,21)).2 := by
    intro i hi
    rw [coreAlpha_rev p (by omega)]
    have e : m-(m-r-6+i+1)=r+5-i := by omega
    simpa only [e] using hb i hi
  have h := hlocal (revSnake p) P (m-r-6) (by omega) hdir hcounts
  rwa [five_sum_rev 12 p r hr] at h

#print axioms share_rev
#print axioms five_sum_rev
#print axioms reverse_rule
end Snake9.LocalWindow.ReverseShareRule
