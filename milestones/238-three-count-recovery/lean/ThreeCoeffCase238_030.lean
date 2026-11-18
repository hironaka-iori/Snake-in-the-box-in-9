import Std
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace CubeInverse
theorem coeff_030 (x y z s t u : Int)
    (hx : -9 ≤ x ∧ x ≤ 9) (hy : -9 ≤ y ∧ y ≤ 9)
    (hz : -9 ≤ z ∧ z ≤ 9)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (hu : -1 ≤ u ∧ u ≤ 1)
    (h1 : 128*x + (0)*y + (8)*z = 315*s)
    (h2 : (0)*x + 128*y + (0)*z = 315*t)
    (h3 : (8)*x + (0)*y + 128*z = 315*u) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have ex : 2088960*x = (16384)*(128*x+(0)*y+(8)*z) + (0)*((0)*x+128*y+(0)*z) + (-1024)*((8)*x+(0)*y+128*z) := by
    clear h1 h2 h3 hx hy hz hs ht hu
    omega
  rw [h1,h2,h3] at ex
  have ey : 2088960*y = (0)*(128*x+(0)*y+(8)*z) + (16320)*((0)*x+128*y+(0)*z) + (0)*((8)*x+(0)*y+128*z) := by
    clear h1 h2 h3 hx hy hz hs ht hu
    omega
  rw [h1,h2,h3] at ey
  have ez : 2088960*z = (-1024)*(128*x+(0)*y+(8)*z) + (0)*((0)*x+128*y+(0)*z) + (16384)*((8)*x+(0)*y+128*z) := by
    clear h1 h2 h3 hx hy hz hs ht hu
    omega
  rw [h1,h2,h3] at ez
  have sc : s = -1 ∨ s = 0 ∨ s = 1 := by
    clear h1 h2 h3 hx hy hz ht hu ex ey ez
    omega
  have tc : t = -1 ∨ t = 0 ∨ t = 1 := by
    clear h1 h2 h3 hx hy hz hs hu ex ey ez
    omega
  have uc : u = -1 ∨ u = 0 ∨ u = 1 := by
    clear h1 h2 h3 hx hy hz hs ht ex ey ez
    omega
  rcases sc with rfl | rfl | rfl <;>
    rcases tc with rfl | rfl | rfl <;>
    rcases uc with rfl | rfl | rfl <;>
      clear h1 h2 h3 <;> omega
#print axioms coeff_030
end CubeInverse
