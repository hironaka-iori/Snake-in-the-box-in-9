import Std
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace CubeInverse
theorem coeff_304 (x y z s t u : Int)
    (hx : -9 ≤ x ∧ x ≤ 9) (hy : -9 ≤ y ∧ y ≤ 9)
    (hz : -9 ≤ z ∧ z ≤ 9)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (hu : -1 ≤ u ∧ u ≤ 1)
    (h1 : 128*x + (8)*y + (0)*z = 315*s)
    (h2 : (8)*x + 128*y + (-16)*z = 315*t)
    (h3 : (0)*x + (-16)*y + 128*z = 315*u) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have sc : s = -1 ∨ s = 0 ∨ s = 1 := by omega
  have tc : t = -1 ∨ t = 0 ∨ t = 1 := by omega
  have uc : u = -1 ∨ u = 0 ∨ u = 1 := by omega
  rcases sc with rfl | rfl | rfl <;>
    rcases tc with rfl | rfl | rfl <;>
    rcases uc with rfl | rfl | rfl <;> omega
#print axioms coeff_304
end CubeInverse
