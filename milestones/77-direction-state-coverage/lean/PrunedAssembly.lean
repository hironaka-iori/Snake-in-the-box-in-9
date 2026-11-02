import PrunedEnumeration

namespace Snake9.Direction77
open Snake9.WindowAutomaton

theorem allBelow_complete (n : Nat) (p : Nat → Bool)
    (h : ∀ a, a < n → p a = true) : allBelow n p = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := ih (fun a ha => h a (by omega))
    simp only [allBelow, hn, h n (by omega), Bool.and_self]

theorem allPruned_step (n bound : Nat) (pre : List Nat) (p : List Nat → Bool)
    (h : ∀ a, a < bound+1 → allPruned n
      (if bound < a+1 then a+1 else bound) (pre ++ [a]) p = true) :
    allPruned (n+1) bound pre p = true := by
  have hs := allBelow_complete (bound+1) _ h
  rw [allPruned, hs]
  simp

#print axioms allBelow_complete
#print axioms allPruned_step
end Snake9.Direction77
