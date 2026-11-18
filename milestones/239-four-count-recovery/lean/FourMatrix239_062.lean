import Std
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace FourRecovery239
private theorem ternary_mem (s : Int) (h : -1 ≤ s ∧ s ≤ 1) : s ∈ ([-1,0,1] : List Int) := by
  simp
  omega
private theorem row_0 (x0 x1 x2 x3 : Int) : 222829785*x0 = (1913760)*((128)*x0 + (-16)*x1 + (-10)*x2 + (35)*x3) + (160920)*((-16)*x0 + (128)*x1 + (35)*x2 + (-10)*x3) + (137970)*((-10)*x0 + (35)*x1 + (128)*x2 + (8)*x3) + (-519345)*((35)*x0 + (-10)*x1 + (8)*x2 + (128)*x3) := by omega
private theorem row_1 (x0 x1 x2 x3 : Int) : 222829785*x1 = (160920)*((128)*x0 + (-16)*x1 + (-10)*x2 + (35)*x3) + (1913760)*((-16)*x0 + (128)*x1 + (35)*x2 + (-10)*x3) + (-519345)*((-10)*x0 + (35)*x1 + (128)*x2 + (8)*x3) + (137970)*((35)*x0 + (-10)*x1 + (8)*x2 + (128)*x3) := by omega
private theorem row_2 (x0 x1 x2 x3 : Int) : 222829785*x2 = (137970)*((128)*x0 + (-16)*x1 + (-10)*x2 + (35)*x3) + (-519345)*((-16)*x0 + (128)*x1 + (35)*x2 + (-10)*x3) + (1905984)*((-10)*x0 + (35)*x1 + (128)*x2 + (8)*x3) + (-197424)*((35)*x0 + (-10)*x1 + (8)*x2 + (128)*x3) := by omega
private theorem row_3 (x0 x1 x2 x3 : Int) : 222829785*x3 = (-519345)*((128)*x0 + (-16)*x1 + (-10)*x2 + (35)*x3) + (137970)*((-16)*x0 + (128)*x1 + (35)*x2 + (-10)*x3) + (-197424)*((-10)*x0 + (35)*x1 + (128)*x2 + (8)*x3) + (1905984)*((35)*x0 + (-10)*x1 + (8)*x2 + (128)*x3) := by omega
private theorem admissible :
    ∀ s0 ∈ ([-1,0,1] : List Int),
    ∀ s1 ∈ ([-1,0,1] : List Int),
    ∀ s2 ∈ ([-1,0,1] : List Int),
    ∀ s3 ∈ ([-1,0,1] : List Int),
    (222829785 ∣ ((1913760)*(315*s0) + (160920)*(315*s1) + (137970)*(315*s2) + (-519345)*(315*s3))) →
    (222829785 ∣ ((160920)*(315*s0) + (1913760)*(315*s1) + (-519345)*(315*s2) + (137970)*(315*s3))) →
    (222829785 ∣ ((137970)*(315*s0) + (-519345)*(315*s1) + (1905984)*(315*s2) + (-197424)*(315*s3))) →
    (222829785 ∣ ((-519345)*(315*s0) + (137970)*(315*s1) + (-197424)*(315*s2) + (1905984)*(315*s3))) →
    s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 := by decide
theorem zero_solution_062 (x0 x1 x2 x3 s0 s1 s2 s3 : Int)
    (hs0 : -1 ≤ s0 ∧ s0 ≤ 1)
    (hs1 : -1 ≤ s1 ∧ s1 ≤ 1)
    (hs2 : -1 ≤ s2 ∧ s2 ≤ 1)
    (hs3 : -1 ≤ s3 ∧ s3 ≤ 1)
    (h0 : (128)*x0 + (-16)*x1 + (-10)*x2 + (35)*x3 = 315*s0)
    (h1 : (-16)*x0 + (128)*x1 + (35)*x2 + (-10)*x3 = 315*s1)
    (h2 : (-10)*x0 + (35)*x1 + (128)*x2 + (8)*x3 = 315*s2)
    (h3 : (35)*x0 + (-10)*x1 + (8)*x2 + (128)*x3 = 315*s3)
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
#print axioms zero_solution_062
end FourRecovery239
