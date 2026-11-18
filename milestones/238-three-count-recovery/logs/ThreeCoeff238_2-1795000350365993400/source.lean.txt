import ThreeCoeffCase238_200
import ThreeCoeffCase238_201
import ThreeCoeffCase238_202
import ThreeCoeffCase238_203
import ThreeCoeffCase238_204
import ThreeCoeffCase238_210
import ThreeCoeffCase238_211
import ThreeCoeffCase238_212
import ThreeCoeffCase238_213
import ThreeCoeffCase238_214
import ThreeCoeffCase238_220
import ThreeCoeffCase238_221
import ThreeCoeffCase238_222
import ThreeCoeffCase238_223
import ThreeCoeffCase238_224
import ThreeCoeffCase238_230
import ThreeCoeffCase238_231
import ThreeCoeffCase238_232
import ThreeCoeffCase238_233
import ThreeCoeffCase238_234
import ThreeCoeffCase238_240
import ThreeCoeffCase238_241
import ThreeCoeffCase238_242
import ThreeCoeffCase238_243
import ThreeCoeffCase238_244
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace CubeInverse
theorem three_coeff_2 (b c x y z s t u : Int)
    (hb : b ∈ ([0,35,-10,8,-16] : List Int))
    (hc : c ∈ ([0,35,-10,8,-16] : List Int))
    (hx : -9 ≤ x ∧ x ≤ 9) (hy : -9 ≤ y ∧ y ≤ 9)
    (hz : -9 ≤ z ∧ z ≤ 9)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (hu : -1 ≤ u ∧ u ≤ 1)
    (h1 : 128*x + (-10)*y + b*z = 315*s)
    (h2 : (-10)*x + 128*y + c*z = 315*t)
    (h3 : b*x + c*y + 128*z = 315*u) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  simp at hb hc
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact coeff_200 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_201 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_202 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_203 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_204 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_210 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_211 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_212 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_213 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_214 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_220 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_221 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_222 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_223 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_224 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_230 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_231 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_232 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_233 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_234 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_240 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_241 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_242 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_243 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_244 x y z s t u hx hy hz hs ht hu h1 h2 h3
#print axioms three_coeff_2
end CubeInverse
