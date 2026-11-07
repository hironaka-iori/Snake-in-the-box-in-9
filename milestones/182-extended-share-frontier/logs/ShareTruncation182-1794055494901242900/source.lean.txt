import Std
namespace ShareTruncation182

theorem bounded_sum (xs : List Nat) (K : Nat) :
    (xs.map (fun s => min s (K+1))).sum≤K ↔ xs.sum≤K := by
  have forward : ∀ ys : List Nat,
      (ys.map (fun s => min s (K+1))).sum≤K →
      (ys.map (fun s => min s (K+1))).sum=ys.sum := by
    intro ys
    induction ys with
    | nil => simp
    | cons a ys ih =>
      intro h
      simp only [List.map_cons,List.sum_cons] at h ⊢
      have ha : a≤K := by
        by_cases hn : a≤K
        · exact hn
        · have hmin : min a (K+1)=K+1 := Nat.min_eq_right (by omega)
          rw [hmin] at h
          omega
      have ht := ih (by omega)
      rw [Nat.min_eq_left (by omega),ht]
  have backward : ∀ ys : List Nat,
      (ys.map (fun s => min s (K+1))).sum≤ys.sum := by
    intro ys
    induction ys with
    | nil => simp
    | cons a ys ih =>
      simp only [List.map_cons,List.sum_cons]
      exact Nat.add_le_add (Nat.min_le_left _ _) ih
  constructor
  · intro h
    rw [←forward xs h]
    exact h
  · intro h
    exact Nat.le_trans (backward xs) h

theorem cap_fourteen_exact (shares : List Nat) :
    (shares.map (fun s => min s 15)).sum≤14 ↔ shares.sum≤14 :=
  bounded_sum shares 14

#print axioms bounded_sum
#print axioms cap_fourteen_exact
end ShareTruncation182
