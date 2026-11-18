import Std
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace FourRecovery239
private theorem ternary_mem (s : Int) (h : -1 ≤ s ∧ s ≤ 1) : s ∈ ([-1,0,1] : List Int) := by
  simp
  omega
private theorem row_0 (x0 x1 x2 x3 : Int) : 241164864*x0 = (1928448)*((128)*x0 + (-16)*x1 + (8)*x2 + (-10)*x3) + (222912)*((-16)*x0 + (128)*x1 + (8)*x2 + (35)*x3) + (-140616)*((8)*x0 + (8)*x1 + (128)*x2 + (8)*x3) + (98496)*((-10)*x0 + (35)*x1 + (8)*x2 + (128)*x3) := by omega
private theorem row_1 (x0 x1 x2 x3 : Int) : 241164864*x1 = (222912)*((128)*x0 + (-16)*x1 + (8)*x2 + (-10)*x3) + (2066688)*((-16)*x0 + (128)*x1 + (8)*x2 + (35)*x3) + (-109296)*((8)*x0 + (8)*x1 + (128)*x2 + (8)*x3) + (-540864)*((-10)*x0 + (35)*x1 + (8)*x2 + (128)*x3) := by omega
private theorem row_2 (x0 x1 x2 x3 : Int) : 241164864*x2 = (-140616)*((128)*x0 + (-16)*x1 + (8)*x2 + (-10)*x3) + (-109296)*((-16)*x0 + (128)*x1 + (8)*x2 + (35)*x3) + (1905984)*((8)*x0 + (8)*x1 + (128)*x2 + (8)*x3) + (-100224)*((-10)*x0 + (35)*x1 + (8)*x2 + (128)*x3) := by omega
private theorem row_3 (x0 x1 x2 x3 : Int) : 241164864*x3 = (98496)*((128)*x0 + (-16)*x1 + (8)*x2 + (-10)*x3) + (-540864)*((-16)*x0 + (128)*x1 + (8)*x2 + (35)*x3) + (-100224)*((8)*x0 + (8)*x1 + (128)*x2 + (8)*x3) + (2045952)*((-10)*x0 + (35)*x1 + (8)*x2 + (128)*x3) := by omega
private theorem admissible :
    ∀ s0 ∈ ([-1,0,1] : List Int),
    ∀ s1 ∈ ([-1,0,1] : List Int),
    ∀ s2 ∈ ([-1,0,1] : List Int),
    ∀ s3 ∈ ([-1,0,1] : List Int),
    (241164864 ∣ ((1928448)*(315*s0) + (222912)*(315*s1) + (-140616)*(315*s2) + (98496)*(315*s3))) →
    (241164864 ∣ ((222912)*(315*s0) + (2066688)*(315*s1) + (-109296)*(315*s2) + (-540864)*(315*s3))) →
    (241164864 ∣ ((-140616)*(315*s0) + (-109296)*(315*s1) + (1905984)*(315*s2) + (-100224)*(315*s3))) →
    (241164864 ∣ ((98496)*(315*s0) + (-540864)*(315*s1) + (-100224)*(315*s2) + (2045952)*(315*s3))) →
    s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 := by decide
theorem zero_solution_038 (x0 x1 x2 x3 s0 s1 s2 s3 : Int)
    (hs0 : -1 ≤ s0 ∧ s0 ≤ 1)
    (hs1 : -1 ≤ s1 ∧ s1 ≤ 1)
    (hs2 : -1 ≤ s2 ∧ s2 ≤ 1)
    (hs3 : -1 ≤ s3 ∧ s3 ≤ 1)
    (h0 : (128)*x0 + (-16)*x1 + (8)*x2 + (-10)*x3 = 315*s0)
    (h1 : (-16)*x0 + (128)*x1 + (8)*x2 + (35)*x3 = 315*s1)
    (h2 : (8)*x0 + (8)*x1 + (128)*x2 + (8)*x3 = 315*s2)
    (h3 : (-10)*x0 + (35)*x1 + (8)*x2 + (128)*x3 = 315*s3)
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
#print axioms zero_solution_038
end FourRecovery239
