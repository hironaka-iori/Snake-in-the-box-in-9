import CubeInverse
import ThreeCoefficients238

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

namespace CubeInverse

/-- A signed difference of binary selections cannot have its neighbour-sum
profile supported on three distinct vertices of the actual nine-bit cube. -/
theorem three_erasures (z : Vertex 9 → Int)
    (hz : ∀ x, -1 ≤ z x ∧ z x ≤ 1)
    (a b c : Vertex 9) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (away : ∀ x, x ≠ a → x ≠ b → x ≠ c → flipSum 9 z x = 0) :
    z = fun _ => 0 := by
  let v := flipSum 9 z
  have obs : flipSum 9 z = fun x =>
      (if x = a then v a else 0) + (if x = b then v b else 0) +
        (if x = c then v c else 0) := by
    funext x
    by_cases ha : x = a
    · subst x; simp [hab, hac, v]
    by_cases hb : x = b
    · subst x; simp [Ne.symm hab, hbc, v]
    by_cases hc : x = c
    · subst x; simp [Ne.symm hac, Ne.symm hbc, v]
    simp [ha, hb, hc, away x ha hb hc]
  have row (p : Vertex 9) :
      kernel p a * v a + kernel p b * v b + kernel p c * v c =
        315 * z p := by
    have h := reconstruct z p
    rw [obs, inner_add_r, inner_add_r, inner_mass, inner_mass, inner_mass] at h
    exact h
  have r := row (antipode 9 a)
  have s := row (antipode 9 b)
  have t := row (antipode 9 c)
  rw [anti_diag] at r s t
  rw [anti_symm b a] at s
  rw [anti_symm c a, anti_symm c b] at t
  obtain ⟨za, zb, zc⟩ := three_coeff
    (kernel (antipode 9 a) b)
    (kernel (antipode 9 a) c)
    (kernel (antipode 9 b) c)
    (v a) (v b) (v c)
    (z (antipode 9 a)) (z (antipode 9 b)) (z (antipode 9 c))
    (anti_off a b hab) (anti_off a c hac) (anti_off b c hbc)
    (flip_bound 9 z hz a) (flip_bound 9 z hz b) (flip_bound 9 z hz c)
    (hz _) (hz _) (hz _) r s t
  funext p
  have h := row p
  change v a = 0 at za
  change v b = 0 at zb
  change v c = 0 at zc
  simp only [za, zb, zc, Int.mul_zero, Int.add_zero] at h
  omega

theorem flip_sub_three (n : Nat) (f g : Vertex n → Int) (a : Vertex n) :
    flipSum n (fun x => f x - g x) a = flipSum n f a - flipSum n g a := by
  induction n with
  | zero => simp [flipSum]
  | succ n ih =>
    rcases a with ⟨b, a⟩
    simp only [flipSum]
    rw [ih (fun y => f (b, y)) (fun y => g (b, y))]
    omega

/-- Agreement on any 509 specified neighbour counts uniquely determines
a binary selection on the actual nine-bit cube. -/
theorem determine_selection_three (f g : Vertex 9 → Bool)
    (a b c : Vertex 9) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (agree : ∀ x, x ≠ a → x ≠ b → x ≠ c →
      flipSum 9 (indicator f) x = flipSum 9 (indicator g) x) : f = g := by
  let z := fun x => indicator f x - indicator g x
  have bounded (x) : -1 ≤ z x ∧ z x ≤ 1 := by
    cases hf : f x <;> cases hg : g x <;> simp [z, indicator, hf, hg]
  have away (x) (ha : x ≠ a) (hb : x ≠ b) (hc : x ≠ c) :
      flipSum 9 z x = 0 := by
    unfold z
    rw [flip_sub_three, agree x ha hb hc, Int.sub_self]
  have h := three_erasures z bounded a b c hab hac hbc away
  funext x
  have zero := congrFun h x
  cases hf : f x <;> cases hg : g x <;> simp [z, indicator, hf, hg] at zero ⊢

#print axioms three_erasures
#print axioms flip_sub_three
#print axioms determine_selection_three

end CubeInverse
