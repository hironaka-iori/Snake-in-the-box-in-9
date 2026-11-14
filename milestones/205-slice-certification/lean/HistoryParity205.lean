import Std
namespace HistoryParity205

theorem xorCancel (b u v : Bool) : Bool.xor (Bool.xor b u) (Bool.xor b v)=Bool.xor u v := by
  cases b <;> cases u <;> cases v <;> rfl
theorem xorSolve (u v d : Bool) (h : Bool.xor u v=d) : v=Bool.xor d u := by
  cases u <;> cases v <;> cases d <;> simp_all

theorem differenceConstant (p q : Nat → Bool) (m : Nat)
    (hp : ∀ i, i<m → p (i+1)=!(p i)) (hq : ∀ i, i<m → q (i+1)=!(q i)) :
    ∀ i, i≤m → Bool.xor (p i) (q i)=Bool.xor (p 0) (q 0) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have step : i<m := by omega
    rw [hp i step,hq i step]
    have h := ih (by omega)
    cases a : p i <;> cases b : q i <;> simpa [a,b] using h

theorem oneBitHistory (base p q : Nat → Bool) (m : Nat)
    (hp : ∀ i, i<m → Bool.xor (base (i+1)) (p (i+1)) = !(Bool.xor (base i) (p i)))
    (hq : ∀ i, i<m → Bool.xor (base (i+1)) (q (i+1)) = !(Bool.xor (base i) (q i))) :
    ∃ d : Bool, ∀ i, i≤m → q i=Bool.xor d (p i) := by
  refine ⟨Bool.xor (p 0) (q 0),?_⟩
  intro i hi
  have h := differenceConstant (fun i => Bool.xor (base i) (p i)) (fun i => Bool.xor (base i) (q i)) m hp hq i hi
  simp only [xorCancel] at h
  exact xorSolve (p i) (q i) _ h

#print axioms xorCancel
#print axioms xorSolve
#print axioms differenceConstant
#print axioms oneBitHistory
end HistoryParity205
