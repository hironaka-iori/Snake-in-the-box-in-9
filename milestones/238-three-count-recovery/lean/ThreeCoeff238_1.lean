import ThreeCoeffCase238_100
import ThreeCoeffCase238_101
import ThreeCoeffCase238_102
import ThreeCoeffCase238_103
import ThreeCoeffCase238_104
import ThreeCoeffCase238_110
import ThreeCoeffCase238_111
import ThreeCoeffCase238_112
import ThreeCoeffCase238_113
import ThreeCoeffCase238_114
import ThreeCoeffCase238_120
import ThreeCoeffCase238_121
import ThreeCoeffCase238_122
import ThreeCoeffCase238_123
import ThreeCoeffCase238_124
import ThreeCoeffCase238_130
import ThreeCoeffCase238_131
import ThreeCoeffCase238_132
import ThreeCoeffCase238_133
import ThreeCoeffCase238_134
import ThreeCoeffCase238_140
import ThreeCoeffCase238_141
import ThreeCoeffCase238_142
import ThreeCoeffCase238_143
import ThreeCoeffCase238_144
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace CubeInverse
theorem three_coeff_1 (b c x y z s t u : Int)
    (hb : b ∈ ([0,35,-10,8,-16] : List Int))
    (hc : c ∈ ([0,35,-10,8,-16] : List Int))
    (hx : -9 ≤ x ∧ x ≤ 9) (hy : -9 ≤ y ∧ y ≤ 9)
    (hz : -9 ≤ z ∧ z ≤ 9)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (hu : -1 ≤ u ∧ u ≤ 1)
    (h1 : 128*x + (35)*y + b*z = 315*s)
    (h2 : (35)*x + 128*y + c*z = 315*t)
    (h3 : b*x + c*y + 128*z = 315*u) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  simp at hb hc
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact coeff_100 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_101 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_102 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_103 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_104 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_110 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_111 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_112 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_113 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_114 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_120 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_121 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_122 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_123 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_124 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_130 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_131 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_132 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_133 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_134 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_140 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_141 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_142 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_143 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_144 x y z s t u hx hy hz hs ht hu h1 h2 h3
#print axioms three_coeff_1
end CubeInverse
