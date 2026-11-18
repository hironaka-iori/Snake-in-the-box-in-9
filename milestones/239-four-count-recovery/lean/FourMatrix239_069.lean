import Std
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace FourRecovery239
private theorem ternary_mem (s : Int) (h : -1 ≤ s ∧ s ≤ 1) : s ∈ ([-1,0,1] : List Int) := by
  simp
  omega
private theorem row_0 (x0 x1 x2 x3 : Int) : 242464320*x0 = (1913760)*((128)*x0 + (8)*x1 + (8)*x2 + (8)*x3) + (-122760)*((8)*x0 + (128)*x1 + (8)*x2 + (-10)*x3) + (-82800)*((8)*x0 + (8)*x1 + (128)*x2 + (35)*x3) + (-106560)*((8)*x0 + (-10)*x1 + (35)*x2 + (128)*x3) := by omega
private theorem row_1 (x0 x1 x2 x3 : Int) : 242464320*x1 = (-122760)*((128)*x0 + (8)*x1 + (8)*x2 + (8)*x3) + (1928448)*((8)*x0 + (128)*x1 + (8)*x2 + (-10)*x3) + (-168768)*((8)*x0 + (8)*x1 + (128)*x2 + (35)*x3) + (204480)*((8)*x0 + (-10)*x1 + (35)*x2 + (128)*x3) := by omega
private theorem row_2 (x0 x1 x2 x3 : Int) : 242464320*x2 = (-82800)*((128)*x0 + (8)*x1 + (8)*x2 + (8)*x3) + (-168768)*((8)*x0 + (128)*x1 + (8)*x2 + (-10)*x3) + (2066688)*((8)*x0 + (8)*x1 + (128)*x2 + (35)*x3) + (-573120)*((8)*x0 + (-10)*x1 + (35)*x2 + (128)*x3) := by omega
private theorem row_3 (x0 x1 x2 x3 : Int) : 242464320*x3 = (-106560)*((128)*x0 + (8)*x1 + (8)*x2 + (8)*x3) + (204480)*((8)*x0 + (128)*x1 + (8)*x2 + (-10)*x3) + (-573120)*((8)*x0 + (8)*x1 + (128)*x2 + (35)*x3) + (2073600)*((8)*x0 + (-10)*x1 + (35)*x2 + (128)*x3) := by omega
private theorem admissible :
    ∀ s0 ∈ ([-1,0,1] : List Int),
    ∀ s1 ∈ ([-1,0,1] : List Int),
    ∀ s2 ∈ ([-1,0,1] : List Int),
    ∀ s3 ∈ ([-1,0,1] : List Int),
    (242464320 ∣ ((1913760)*(315*s0) + (-122760)*(315*s1) + (-82800)*(315*s2) + (-106560)*(315*s3))) →
    (242464320 ∣ ((-122760)*(315*s0) + (1928448)*(315*s1) + (-168768)*(315*s2) + (204480)*(315*s3))) →
    (242464320 ∣ ((-82800)*(315*s0) + (-168768)*(315*s1) + (2066688)*(315*s2) + (-573120)*(315*s3))) →
    (242464320 ∣ ((-106560)*(315*s0) + (204480)*(315*s1) + (-573120)*(315*s2) + (2073600)*(315*s3))) →
    s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 := by decide
theorem zero_solution_069 (x0 x1 x2 x3 s0 s1 s2 s3 : Int)
    (hs0 : -1 ≤ s0 ∧ s0 ≤ 1)
    (hs1 : -1 ≤ s1 ∧ s1 ≤ 1)
    (hs2 : -1 ≤ s2 ∧ s2 ≤ 1)
    (hs3 : -1 ≤ s3 ∧ s3 ≤ 1)
    (h0 : (128)*x0 + (8)*x1 + (8)*x2 + (8)*x3 = 315*s0)
    (h1 : (8)*x0 + (128)*x1 + (8)*x2 + (-10)*x3 = 315*s1)
    (h2 : (8)*x0 + (8)*x1 + (128)*x2 + (35)*x3 = 315*s2)
    (h3 : (8)*x0 + (-10)*x1 + (35)*x2 + (128)*x3 = 315*s3)
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
#print axioms zero_solution_069
end FourRecovery239
