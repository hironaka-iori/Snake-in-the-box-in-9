import Std
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace CubeInverse
theorem coeff_412 (x y z s t u : Int)
    (hx : -9 ≤ x ∧ x ≤ 9) (hy : -9 ≤ y ∧ y ≤ 9)
    (hz : -9 ≤ z ∧ z ≤ 9)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (hu : -1 ≤ u ∧ u ≤ 1)
    (h1 : 128*x + (-16)*y + (35)*z = 315*s)
    (h2 : (-16)*x + 128*y + (-10)*z = 315*t)
    (h3 : (35)*x + (-10)*y + 128*z = 315*u) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have ex : 1905984*x = (16284)*(128*x+(-16)*y+(35)*z) + (1698)*((-16)*x+128*y+(-10)*z) + (-4320)*((35)*x+(-10)*y+128*z) := by
    clear h1 h2 h3 hx hy hz hs ht hu
    omega
  rw [h1,h2,h3] at ex
  have ey : 1905984*y = (1698)*(128*x+(-16)*y+(35)*z) + (15159)*((-16)*x+128*y+(-10)*z) + (720)*((35)*x+(-10)*y+128*z) := by
    clear h1 h2 h3 hx hy hz hs ht hu
    omega
  rw [h1,h2,h3] at ey
  have ez : 1905984*z = (-4320)*(128*x+(-16)*y+(35)*z) + (720)*((-16)*x+128*y+(-10)*z) + (16128)*((35)*x+(-10)*y+128*z) := by
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
#print axioms coeff_412
end CubeInverse
