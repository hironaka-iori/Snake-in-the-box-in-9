import Std
namespace SquareChoice192

def conflict (u v : Nat) : Bool :=
  (u == v) || (List.range 9).any (fun k => v == Nat.xor u (2^k))

def pick (p a : Nat → Nat) (x : Nat → Bool) (i : Nat) : Nat :=
  if x i then a i else p i

theorem forceOld (p a : Nat → Nat) (x : Nat → Bool) (w i : Nat)
    (h : conflict w (pick p a x i)=false)
    (hb : conflict w (p i)=true) : x i=true := by
  cases hx : x i
  · simp only [pick, hx, Bool.false_eq_true, if_false] at h
    rw [hb] at h
    contradiction
  · rfl

theorem forbidNew (p a : Nat → Nat) (x : Nat → Bool) (w i : Nat)
    (h : conflict w (pick p a x i)=false)
    (hb : conflict w (a i)=true) : x i=false := by
  cases hx : x i
  · rfl
  · simp only [pick, hx, if_true] at h
    rw [hb] at h
    contradiction

theorem propagate (p a : Nat → Nat) (x : Nat → Bool) (i j : Nat)
    (h : conflict (pick p a x i) (pick p a x j)=false)
    (hb : conflict (a i) (p j)=true) (hi : x i=true) : x j=true := by
  cases hj : x j
  · simp only [pick, hi, hj, if_true, Bool.false_eq_true, if_false] at h
    rw [hb] at h
    contradiction
  · rfl

theorem pairImpossible (p a : Nat → Nat) (x : Nat → Bool) (i j : Nat)
    (h : conflict (pick p a x i) (pick p a x j)=false)
    (hb : conflict (a i) (a j)=true) (hi : x i=true) (hj : x j=true) : False := by
  simp only [pick, hi, hj, if_true] at h
  rw [hb] at h
  contradiction

#print axioms forceOld
#print axioms forbidNew
#print axioms propagate
#print axioms pairImpossible
end SquareChoice192
