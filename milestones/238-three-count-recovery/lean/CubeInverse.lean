import CubeInverseRecovery237

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

namespace CubeInverse

private theorem two_coeff (c x y s t : Int) (hc : c ∈ ([0,35,-10,8,-16] : List Int))
    (hx : -9 ≤ x ∧ x ≤ 9) (hy : -9 ≤ y ∧ y ≤ 9)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (h1 : 128*x + c*y = 315*s) (h2 : c*x + 128*y = 315*t) :
    x = 0 ∧ y = 0 := by
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    have s_cases : s = -1 ∨ s = 0 ∨ s = 1 := by omega
  all_goals rcases s_cases with rfl | rfl | rfl <;>
    have t_cases : t = -1 ∨ t = 0 ∨ t = 1 := by omega
  all_goals rcases t_cases with rfl | rfl | rfl <;> omega

/-- A signed difference of binary selections cannot have its neighbour-sum
profile supported on at most two arbitrary vertices. -/
theorem two_erasures (z : Vertex 9 → Int) (hz : ∀ x, -1 ≤ z x ∧ z x ≤ 1)
    (a b : Vertex 9) (hab : a ≠ b)
    (away : ∀ x, x ≠ a → x ≠ b → flipSum 9 z x = 0) :
    z = fun _ => 0 := by
  let v := flipSum 9 z
  have obs : flipSum 9 z = fun x =>
      (if x = a then v a else 0) + (if x = b then v b else 0) := by
    funext x
    by_cases ha : x = a
    · subst x; simp [hab, v]
    by_cases hb : x = b
    · subst x; simp [Ne.symm hab, v]
    simp [ha, hb, away x ha hb]
  have row (p : Vertex 9) : kernel p a * v a + kernel p b * v b = 315 * z p := by
    have h := reconstruct z p
    rw [obs, inner_add_r, inner_mass, inner_mass] at h
    exact h
  have r := row (antipode 9 a)
  have s := row (antipode 9 b)
  rw [anti_diag] at r s
  rw [anti_symm b a] at s
  obtain ⟨za,zb⟩ := two_coeff _ _ _ _ _ (anti_off a b hab)
    (flip_bound 9 z hz a) (flip_bound 9 z hz b) (hz _) (hz _) r s
  funext p
  have h := row p
  change v a = 0 at za
  change v b = 0 at zb
  rw [za,zb,Int.mul_zero,Int.mul_zero,Int.add_zero] at h
  omega

#print axioms two_erasures

def indicator (f : Vertex 9 → Bool) (x : Vertex 9) : Int := if f x then 1 else 0

private theorem flip_sub (n : Nat) (f g : Vertex n → Int) (a : Vertex n) :
    flipSum n (fun x => f x - g x) a = flipSum n f a - flipSum n g a := by
  induction n with
  | zero => simp [flipSum]
  | succ n ih =>
    rcases a with ⟨b,a⟩
    simp only [flipSum]
    rw [ih (fun y => f (b,y)) (fun y => g (b,y))]
    omega

theorem determine_selection (f g : Vertex 9 → Bool) (a b : Vertex 9) (hab : a ≠ b)
    (agree : ∀ x, x ≠ a → x ≠ b →
      flipSum 9 (indicator f) x = flipSum 9 (indicator g) x) : f = g := by
  let z := fun x => indicator f x - indicator g x
  have bounded (x) : -1 ≤ z x ∧ z x ≤ 1 := by
    cases hf : f x <;> cases hg : g x <;> simp [z,indicator,hf,hg]
  have away (x) (ha : x ≠ a) (hb : x ≠ b) : flipSum 9 z x = 0 := by
    unfold z
    rw [flip_sub, agree x ha hb, Int.sub_self]
  have h := two_erasures z bounded a b hab away
  funext x
  have zero := congrFun h x
  cases hf : f x <;> cases hg : g x <;> simp [z,indicator,hf,hg] at zero ⊢

#print axioms determine_selection

end CubeInverse
