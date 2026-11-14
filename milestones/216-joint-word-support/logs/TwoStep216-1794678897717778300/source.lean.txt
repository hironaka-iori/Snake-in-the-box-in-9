import PathParity214

set_option Elab.async false

namespace TwoStep216
open IndexedCriterion206

/-- Triangle inequality for equal-length Boolean words. -/
theorem hamming_triangle (u v w : List Bool)
    (huv : u.length = v.length) (hvw : v.length = w.length) :
    hamming u w ≤ hamming u v + hamming v w := by
  induction u generalizing v w with
  | nil => cases v <;> cases w <;> simp_all [hamming]
  | cons a us ih =>
      cases v with
      | nil => simp at huv
      | cons b vs =>
          cases w with
          | nil => simp at hvw
          | cons c ws =>
              have htuv : us.length = vs.length := Nat.succ.inj huv
              have htvw : vs.length = ws.length := Nat.succ.inj hvw
              have ht := ih vs ws htuv htvw
              cases a <;> cases b <;> cases c <;>
                simp [hamming] <;> omega

/-- Two consecutive cube edges either return to the initial word
or leave an outer Hamming distance of two. -/
theorem two_step_distance (u v w : List Bool)
    (huv : u.length = v.length) (hvw : v.length = w.length)
    (hd01 : hamming u v = 1) (hd12 : hamming v w = 1) :
    hamming u w = 0 ∨ hamming u w = 2 := by
  have hbound : hamming u w ≤ 2 := by
    have ht := hamming_triangle u v w huv hvw
    omega
  by_cases hzero : hamming u w = 0
  · exact Or.inl hzero
  by_cases htwo : hamming u w = 2
  · exact Or.inr htwo
  have hone : hamming u w = 1 := by omega
  have hp01 := WordParity214.adjacent_parity u v huv hd01
  have hp12 := WordParity214.adjacent_parity v w hvw hd12
  have hp02 := WordParity214.adjacent_parity u w (huv.trans hvw) hone
  have hsame : WordParity214.parity w = WordParity214.parity u := by
    simpa [hp01] using hp12
  have himpossible :
      WordParity214.parity u = !(WordParity214.parity u) := hsame.symm.trans hp02
  cases hp : WordParity214.parity u <;> simp [hp] at himpossible

theorem two_step_distance_of_ne (u v w : List Bool)
    (huv : u.length = v.length) (hvw : v.length = w.length)
    (hd01 : hamming u v = 1) (hd12 : hamming v w = 1)
    (hne : u ≠ w) : hamming u w = 2 := by
  rcases two_step_distance u v w huv hvw hd01 hd12 with hzero | htwo
  · exact False.elim (hne ((hamming_eq_zero_iff u w).mp hzero))
  · exact htwo

open ConcreteGeometry213 ConcreteParity214

/-- The literal reconstructed path gives this consequence for each
three successive groups. No normalization or raw-Nat bound is needed. -/
theorem free_two_step_distance (values : Nat → Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ word (values (group i))))
    (g : Nat) (hg : g < 76) :
    hamming (word (values g)) (word (values (g+2))) = 0 ∨
      hamming (word (values g)) (word (values (g+2))) = 2 := by
  have h01 := PathParity214.free_adjacent values hp g (by omega)
  have h12 : hamming (word (values (g+1))) (word (values (g+2))) = 1 := by
    simpa [Nat.add_assoc] using
      PathParity214.free_adjacent values hp (g+1) (by omega)
  exact two_step_distance (word (values g)) (word (values (g+1)))
    (word (values (g+2))) (by simp [word]) (by simp [word]) h01 h12

/-- The distance-two conclusion needs distinct decoded outer words. -/
theorem free_two_step_distance_of_ne (values : Nat → Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ word (values (group i))))
    (g : Nat) (hg : g < 76)
    (hne : word (values g) ≠ word (values (g+2))) :
    hamming (word (values g)) (word (values (g+2))) = 2 := by
  rcases free_two_step_distance values hp g hg with hzero | htwo
  · exact False.elim (hne ((hamming_eq_zero_iff _ _).mp hzero))
  · exact htwo

#print axioms hamming_triangle
#print axioms two_step_distance
#print axioms two_step_distance_of_ne
#print axioms free_two_step_distance
#print axioms free_two_step_distance_of_ne

end TwoStep216
