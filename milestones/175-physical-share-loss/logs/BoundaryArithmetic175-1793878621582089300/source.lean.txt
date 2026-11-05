import Std
namespace BoundaryArithmetic175
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem triple_bound (a b c : Nat)
    (hp : 1≤a ∧ 1≤b ∧ 1≤c)
    (hab : (a=1 → 4≤b) ∧ (b=1 → 4≤a))
    (hbc : (b=1 → 4≤c) ∧ (c=1 → 4≤b))
    (hn : ¬(a=2 ∧ b=2 ∧ c=2)) :
    6≤a+b+c ∧ (a+b+c=6 → a=1 ∧ b=4 ∧ c=1) := by omega

private theorem four_bound (a b c d : Nat)
    (hp : 1≤a ∧ 1≤b ∧ 1≤c ∧ 1≤d)
    (hab : (a=1 → 4≤b) ∧ (b=1 → 4≤a))
    (hbc : (b=1 → 4≤c) ∧ (c=1 → 4≤b))
    (hcd : (c=1 → 4≤d) ∧ (d=1 → 4≤c))
    (hn : ¬(a=2 ∧ b=2 ∧ c=2)) : 9≤a+b+c+d := by omega

theorem seven_count_minimum (a b c d e f g : Nat)
    (hp : 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ 1 ≤ d ∧ 1 ≤ e ∧ 1 ≤ f ∧ 1 ≤ g)
    (hab : (a=1 → 4≤b) ∧ (b=1 → 4≤a))
    (hbc : (b=1 → 4≤c) ∧ (c=1 → 4≤b))
    (hcd : (c=1 → 4≤d) ∧ (d=1 → 4≤c))
    (hde : (d=1 → 4≤e) ∧ (e=1 → 4≤d))
    (hef : (e=1 → 4≤f) ∧ (f=1 → 4≤e))
    (hfg : (f=1 → 4≤g) ∧ (g=1 → 4≤f))
    (h1 : ¬(a=2 ∧ b=2 ∧ c=2)) (h2 : ¬(b=2 ∧ c=2 ∧ d=2))
    (h3 : ¬(c=2 ∧ d=2 ∧ e=2)) (h4 : ¬(d=2 ∧ e=2 ∧ f=2))
    (h5 : ¬(e=2 ∧ f=2 ∧ g=2)) : 16 ≤ a+b+c+d+e+f+g := by
  obtain ⟨ha,hb,hc,hd,he,hf,hg⟩ := hp
  have hfour := four_bound a b c d ⟨ha,hb,hc,hd⟩ hab hbc hcd h1
  have hlast := triple_bound e f g ⟨he,hf,hg⟩ hef hfg h5
  have hfirst := triple_bound a b c ⟨ha,hb,hc⟩ hab hbc h1
  have hlink := hde.2
  omega

theorem stronger_boundary_comparison (m W G L : Nat) (hm : 8 ≤ m)
    (hb : G+840*(m+1)+L ≤ 221136)
    (hp : W+2880 ≤ 5*G)
    (hw : 4462*(m-8) ≤ 9*W+5411) :
    42262*m+45*L ≤ 9928507 := by omega

theorem conditional_upper_234 (m W G L : Nat)
    (hb : G+840*(m+1)+L ≤ 221136)
    (hp : W+2880 ≤ 5*G)
    (hw : 4462*(m-8) ≤ 9*W+5411) : m ≤ 234 := by omega

#print axioms seven_count_minimum
#print axioms stronger_boundary_comparison
#print axioms conditional_upper_234
end BoundaryArithmetic175
