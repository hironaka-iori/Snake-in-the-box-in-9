import ThreeCoeffCase238_400
import ThreeCoeffCase238_401
import ThreeCoeffCase238_402
import ThreeCoeffCase238_403
import ThreeCoeffCase238_404
import ThreeCoeffCase238_410
import ThreeCoeffCase238_411
import ThreeCoeffCase238_412
import ThreeCoeffCase238_413
import ThreeCoeffCase238_414
import ThreeCoeffCase238_420
import ThreeCoeffCase238_421
import ThreeCoeffCase238_422
import ThreeCoeffCase238_423
import ThreeCoeffCase238_424
import ThreeCoeffCase238_430
import ThreeCoeffCase238_431
import ThreeCoeffCase238_432
import ThreeCoeffCase238_433
import ThreeCoeffCase238_434
import ThreeCoeffCase238_440
import ThreeCoeffCase238_441
import ThreeCoeffCase238_442
import ThreeCoeffCase238_443
import ThreeCoeffCase238_444
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace CubeInverse
theorem three_coeff_4 (b c x y z s t u : Int)
    (hb : b ∈ ([0,35,-10,8,-16] : List Int))
    (hc : c ∈ ([0,35,-10,8,-16] : List Int))
    (hx : -9 ≤ x ∧ x ≤ 9) (hy : -9 ≤ y ∧ y ≤ 9)
    (hz : -9 ≤ z ∧ z ≤ 9)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (hu : -1 ≤ u ∧ u ≤ 1)
    (h1 : 128*x + (-16)*y + b*z = 315*s)
    (h2 : (-16)*x + 128*y + c*z = 315*t)
    (h3 : b*x + c*y + 128*z = 315*u) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  simp at hb hc
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact coeff_400 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_401 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_402 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_403 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_404 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_410 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_411 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_412 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_413 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_414 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_420 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_421 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_422 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_423 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_424 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_430 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_431 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_432 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_433 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_434 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_440 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_441 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_442 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_443 x y z s t u hx hy hz hs ht hu h1 h2 h3
  · exact coeff_444 x y z s t u hx hy hz hs ht hu h1 h2 h3
#print axioms three_coeff_4
end CubeInverse
