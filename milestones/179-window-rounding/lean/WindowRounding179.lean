import Std
namespace WindowRounding179

theorem scaled_division (D d e k : Nat) (hd : (D/d)*d=D) :
    (D/d)*k*(12*e)=D*(k*((12*e)/d))+(D/d)*k*((12*e)%d) := by
  calc
    _ = (D/d)*k*((12*e)%d+d*((12*e)/d)) := by rw [Nat.mod_add_div]
    _ = ((D/d)*d)*(k*((12*e)/d))+(D/d)*k*((12*e)%d) := by
      rw [Nat.mul_add]
      ac_rfl
    _ = _ := by rw [hd]

theorem denominator_clearing : ∀ d : Fin 10, 0<d.val → (2520/d.val)*d.val=2520 := by decide

theorem exceptional_error (d r k : Nat) (hr : r=0 ∨ (r=1 ∧ d=5 ∧ k≤2)) :
    (2520/d)*k*r≤1008*r := by
  rcases hr with h | ⟨h,hd,hk⟩
  · simp [h]
  · simp only [h,hd,Nat.mul_one]
    omega

theorem sum_error (xs : List Nat) (b r : Nat → Nat)
    (h : ∀ x ∈ xs,b x≤1008*r x) :
    (xs.map b).sum≤1008*(xs.map r).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem strict_threshold (A S B L : Nat)
    (he : A=2520*S+B) (hb : B≤1008*L) (hl : L≤1)
    (ha : 36288<A) : 15≤S := by omega

theorem zero_loss_threshold (A S B : Nat)
    (he : A=2520*S+B) (hb : B=0) (ha : 35280<A) : 15≤S := by omega

theorem threshold_equality_is_insufficient :
    (36288 : Nat)=2520*14+1008 := by decide

#print axioms scaled_division
#print axioms denominator_clearing
#print axioms exceptional_error
#print axioms sum_error
#print axioms strict_threshold
#print axioms zero_loss_threshold
#print axioms threshold_equality_is_insufficient
end WindowRounding179
