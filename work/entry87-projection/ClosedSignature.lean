import CubeSyndrome

namespace ClosedSignature
open CubeSyndrome

def C (n : Nat) (s : Cube n → Bool) (x : Cube n) : Bool :=
  add (s x) (D n s x)

theorem linearC (n : Nat) (s t : Cube n → Bool) (x : Cube n) :
    C n (fun y => add (s y) (t y)) x = add (C n s x) (C n t x) := by
  unfold C
  rw [linear]
  exact commuteFour (s x) (t x) (D n s x) (D n t x)

theorem fixedSignature (n : Nat) (hn : odd n = true) (s : Cube n → Bool) (x : Cube n) :
    D n (C n s) x = C n s x := by
  change D n (fun y => add (s y) (D n s y)) x = add (s x) (D n s x)
  rw [linear, square, hn]
  cases s x <;> cases D n s x <;> decide

theorem squareZero (n : Nat) (hn : odd n = true) (s : Cube n → Bool) (x : Cube n) :
    C n (C n s) x = false := by
  change add (C n s x) (D n (C n s) x) = false
  rw [fixedSignature n hn]
  cases C n s x <;> decide

theorem toggleKernel (s k : Cube 9 → Bool) (hk : ∀ x, C 9 k x = false) (x : Cube 9) :
    C 9 (fun y => add (s y) (k y)) x = C 9 s x := by
  rw [linearC,hk]
  cases C 9 s x <;> decide

#print axioms linearC
#print axioms fixedSignature
#print axioms squareZero
#print axioms toggleKernel
end ClosedSignature
