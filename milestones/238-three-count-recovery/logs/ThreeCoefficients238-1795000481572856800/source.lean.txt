import ThreeCoeff238_0
import ThreeCoeff238_1
import ThreeCoeff238_2
import ThreeCoeff238_3
import ThreeCoeff238_4
set_option Elab.async false
namespace CubeInverse
theorem three_coeff (a b c x y z s t u : Int)
    (ha : a ∈ ([0,35,-10,8,-16] : List Int))
    (hb : b ∈ ([0,35,-10,8,-16] : List Int))
    (hc : c ∈ ([0,35,-10,8,-16] : List Int))
    (hx : -9 ≤ x ∧ x ≤ 9) (hy : -9 ≤ y ∧ y ≤ 9)
    (hz : -9 ≤ z ∧ z ≤ 9)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (hu : -1 ≤ u ∧ u ≤ 1)
    (h1 : 128*x + a*y + b*z = 315*s)
    (h2 : a*x + 128*y + c*z = 315*t)
    (h3 : b*x + c*y + 128*z = 315*u) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  simp at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact three_coeff_0 b c x y z s t u hb hc hx hy hz hs ht hu h1 h2 h3
  · exact three_coeff_1 b c x y z s t u hb hc hx hy hz hs ht hu h1 h2 h3
  · exact three_coeff_2 b c x y z s t u hb hc hx hy hz hs ht hu h1 h2 h3
  · exact three_coeff_3 b c x y z s t u hb hc hx hy hz hs ht hu h1 h2 h3
  · exact three_coeff_4 b c x y z s t u hb hc hx hy hz hs ht hu h1 h2 h3
#print axioms three_coeff
end CubeInverse
