import Std
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace FourRecovery239
private theorem ternary_mem (s : Int) (h : -1 ≤ s ∧ s ≤ 1) : s ∈ ([-1,0,1] : List Int) := by
  simp
  omega
private theorem row_0 (x0 x1 x2 x3 : Int) : 237505284*x0 = (1905984)*((128)*x0 + (-16)*x1 + (-10)*x2 + (-10)*x3) + (222048)*((-16)*x0 + (128)*x1 + (-10)*x2 + (35)*x3) + (180090)*((-10)*x0 + (-10)*x1 + (128)*x2 + (-16)*x3) + (110700)*((-10)*x0 + (35)*x1 + (-16)*x2 + (128)*x3) := by omega
private theorem row_1 (x0 x1 x2 x3 : Int) : 237505284*x1 = (222048)*((128)*x0 + (-16)*x1 + (-10)*x2 + (-10)*x3) + (2035584)*((-16)*x0 + (128)*x1 + (-10)*x2 + (35)*x3) + (110700)*((-10)*x0 + (-10)*x1 + (128)*x2 + (-16)*x3) + (-525420)*((-10)*x0 + (35)*x1 + (-16)*x2 + (128)*x3) := by omega
private theorem row_2 (x0 x1 x2 x3 : Int) : 237505284*x2 = (180090)*((128)*x0 + (-16)*x1 + (-10)*x2 + (-10)*x3) + (110700)*((-16)*x0 + (128)*x1 + (-10)*x2 + (35)*x3) + (1905984)*((-10)*x0 + (-10)*x1 + (128)*x2 + (-16)*x3) + (222048)*((-10)*x0 + (35)*x1 + (-16)*x2 + (128)*x3) := by omega
private theorem row_3 (x0 x1 x2 x3 : Int) : 237505284*x3 = (110700)*((128)*x0 + (-16)*x1 + (-10)*x2 + (-10)*x3) + (-525420)*((-16)*x0 + (128)*x1 + (-10)*x2 + (35)*x3) + (222048)*((-10)*x0 + (-10)*x1 + (128)*x2 + (-16)*x3) + (2035584)*((-10)*x0 + (35)*x1 + (-16)*x2 + (128)*x3) := by omega
private theorem admissible :
    ∀ s0 ∈ ([-1,0,1] : List Int),
    ∀ s1 ∈ ([-1,0,1] : List Int),
    ∀ s2 ∈ ([-1,0,1] : List Int),
    ∀ s3 ∈ ([-1,0,1] : List Int),
    (237505284 ∣ ((1905984)*(315*s0) + (222048)*(315*s1) + (180090)*(315*s2) + (110700)*(315*s3))) →
    (237505284 ∣ ((222048)*(315*s0) + (2035584)*(315*s1) + (110700)*(315*s2) + (-525420)*(315*s3))) →
    (237505284 ∣ ((180090)*(315*s0) + (110700)*(315*s1) + (1905984)*(315*s2) + (222048)*(315*s3))) →
    (237505284 ∣ ((110700)*(315*s0) + (-525420)*(315*s1) + (222048)*(315*s2) + (2035584)*(315*s3))) →
    s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 := by decide
theorem zero_solution_057 (x0 x1 x2 x3 s0 s1 s2 s3 : Int)
    (hs0 : -1 ≤ s0 ∧ s0 ≤ 1)
    (hs1 : -1 ≤ s1 ∧ s1 ≤ 1)
    (hs2 : -1 ≤ s2 ∧ s2 ≤ 1)
    (hs3 : -1 ≤ s3 ∧ s3 ≤ 1)
    (h0 : (128)*x0 + (-16)*x1 + (-10)*x2 + (-10)*x3 = 315*s0)
    (h1 : (-16)*x0 + (128)*x1 + (-10)*x2 + (35)*x3 = 315*s1)
    (h2 : (-10)*x0 + (-10)*x1 + (128)*x2 + (-16)*x3 = 315*s2)
    (h3 : (-10)*x0 + (35)*x1 + (-16)*x2 + (128)*x3 = 315*s3)
    : x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
  have e0 := row_0 x0 x1 x2 x3
  rw [h0,h1,h2,h3] at e0
  have e1 := row_1 x0 x1 x2 x3
  rw [h0,h1,h2,h3] at e1
  have e2 := row_2 x0 x1 x2 x3
  rw [h0,h1,h2,h3] at e2
  have e3 := row_3 x0 x1 x2 x3
  rw [h0,h1,h2,h3] at e3
  have z := admissible s0 (ternary_mem s0 hs0) s1 (ternary_mem s1 hs1) s2 (ternary_mem s2 hs2) s3 (ternary_mem s3 hs3)
    ⟨x0, e0.symm⟩ ⟨x1, e1.symm⟩ ⟨x2, e2.symm⟩ ⟨x3, e3.symm⟩
  rcases z with ⟨rfl,rfl,rfl,rfl⟩
  clear h0 h1 h2 h3
  omega
#print axioms zero_solution_057
end FourRecovery239
