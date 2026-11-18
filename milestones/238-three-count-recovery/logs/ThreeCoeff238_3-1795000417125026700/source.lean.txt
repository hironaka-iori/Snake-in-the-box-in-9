import ThreeCoeffCase238_300
import ThreeCoeffCase238_301
import ThreeCoeffCase238_302
import ThreeCoeffCase238_303
import ThreeCoeffCase238_304
import ThreeCoeffCase238_310
import ThreeCoeffCase238_311
import ThreeCoeffCase238_312
import ThreeCoeffCase238_313
import ThreeCoeffCase238_314
import ThreeCoeffCase238_320
import ThreeCoeffCase238_321
import ThreeCoeffCase238_322
import ThreeCoeffCase238_323
import ThreeCoeffCase238_324
import ThreeCoeffCase238_330
import ThreeCoeffCase238_331
import ThreeCoeffCase238_332
import ThreeCoeffCase238_333
import ThreeCoeffCase238_334
import ThreeCoeffCase238_340
import ThreeCoeffCase238_341
import ThreeCoeffCase238_342
import ThreeCoeffCase238_343
import ThreeCoeffCase238_344
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace CubeInverse
theorem three_coeff_3 (b c x y z s t u : Int)
    (hb : b ∈ ([0,35,-10,8,-16] : List Int))
    (hc : c ∈ ([0,35,-10,8,-16] : List Int))
    (hx : -9 ≤ x ∧ x ≤ 9) (hy : -9 ≤ y ∧ y ≤ 9)
    (hz : -9 ≤ z ∧ z ≤ 9)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (hu : -1 ≤ u ∧ u ≤ 1)
    (h1 : 128*x + (8)*y + b*z = 315*s)
    (h2 : (8)*x + 128*y + c*z = 315*t)
    (h3 : b*x + c*y + 128*z = 315*u) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  simp at hb hc
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact coeff_300 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_301 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_302 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_303 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_304 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_310 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_311 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_312 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_313 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_314 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_320 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_321 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_322 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_323 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_324 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_330 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_331 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_332 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_333 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_334 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_340 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_341 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_342 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_343 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_344 x y z s t u hx hy hz hs ht hu h1 h2 h3
#print axioms three_coeff_3
end CubeInverse
