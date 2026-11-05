import Std
namespace Snake9.SmallLossArithmetic174

theorem positive_loss_shapes (l : List Nat)
    (hp : ∀ x ∈ l, 0 < x) (hs : l.sum ≤ 3) :
    l = [] ∨ l = [1] ∨ l = [2] ∨ l = [3] ∨ l = [1,1] ∨
    l = [1,2] ∨ l = [2,1] ∨ l = [1,1,1] := by
  cases l with
  | nil => simp
  | cons a rest =>
    have ha : 0 < a := hp a (by simp)
    cases rest with
    | nil =>
      simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at hs
      have hcases : a = 1 ∨ a = 2 ∨ a = 3 := by omega
      rcases hcases with h | h | h <;> simp [h]
    | cons b rest =>
      have hb : 0 < b := hp b (by simp)
      cases rest with
      | nil =>
        simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at hs
        have hcases : (a=1 ∧ b=1) ∨ (a=1 ∧ b=2) ∨ (a=2 ∧ b=1) := by omega
        rcases hcases with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> simp [h1,h2]
      | cons c rest =>
        have hc : 0 < c := hp c (by simp)
        cases rest with
        | nil =>
          simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at hs
          have he : a=1 ∧ b=1 ∧ c=1 := by omega
          simp [he.1,he.2.1,he.2.2]
        | cons d rest =>
          have hd : 0 < d := hp d (by simp)
          simp only [List.sum_cons] at hs
          omega

#print axioms positive_loss_shapes
end Snake9.SmallLossArithmetic174
