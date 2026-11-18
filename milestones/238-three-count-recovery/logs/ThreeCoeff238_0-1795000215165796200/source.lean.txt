import ThreeCoeffCase238_000
import ThreeCoeffCase238_001
import ThreeCoeffCase238_002
import ThreeCoeffCase238_003
import ThreeCoeffCase238_004
import ThreeCoeffCase238_010
import ThreeCoeffCase238_011
import ThreeCoeffCase238_012
import ThreeCoeffCase238_013
import ThreeCoeffCase238_014
import ThreeCoeffCase238_020
import ThreeCoeffCase238_021
import ThreeCoeffCase238_022
import ThreeCoeffCase238_023
import ThreeCoeffCase238_024
import ThreeCoeffCase238_030
import ThreeCoeffCase238_031
import ThreeCoeffCase238_032
import ThreeCoeffCase238_033
import ThreeCoeffCase238_034
import ThreeCoeffCase238_040
import ThreeCoeffCase238_041
import ThreeCoeffCase238_042
import ThreeCoeffCase238_043
import ThreeCoeffCase238_044
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace CubeInverse
theorem three_coeff_0 (b c x y z s t u : Int)
    (hb : b ∈ ([0,35,-10,8,-16] : List Int))
    (hc : c ∈ ([0,35,-10,8,-16] : List Int))
    (hx : -9 ≤ x ∧ x ≤ 9) (hy : -9 ≤ y ∧ y ≤ 9)
    (hz : -9 ≤ z ∧ z ≤ 9)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (hu : -1 ≤ u ∧ u ≤ 1)
    (h1 : 128*x + (0)*y + b*z = 315*s)
    (h2 : (0)*x + 128*y + c*z = 315*t)
    (h3 : b*x + c*y + 128*z = 315*u) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  simp at hb hc
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact coeff_000 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_001 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_002 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_003 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_004 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_010 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_011 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_012 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_013 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_014 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_020 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_021 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_022 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_023 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_024 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_030 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_031 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_032 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_033 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_034 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_040 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_041 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_042 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_043 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_044 x y z s t u hx hy hz hs ht hu h1 h2 h3
#print axioms three_coeff_0
end CubeInverse
