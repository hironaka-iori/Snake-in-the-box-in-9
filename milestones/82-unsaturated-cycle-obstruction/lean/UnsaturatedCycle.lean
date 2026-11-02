import Mathlib.Tactic
namespace Snake9.UnsaturatedObstruction82

def cycleCounts : List (List Nat) := [[5,2,4,5,5,2],[2,4,5,5,2,4],[4,5,5,2,4,5],[5,5,2,4,5,5]]

theorem cycle_counts_below_six :
    ∀ row ∈ cycleCounts, ∀ c ∈ row, c < 6 := by decide

theorem cycle_weight_sum : (252+480+600+600 : Nat) = 4*483 := by decide

theorem cycle_slope (p d x0 x1 x2 x3 : ℚ)
    (h0 : p+x1 ≤ 252*d+x0) (h1 : p+x2 ≤ 480*d+x1)
    (h2 : p+x3 ≤ 600*d+x2) (h3 : p+x0 ≤ 600*d+x3) :
    p ≤ 483*d := by linarith

theorem no_234_criterion (p d R : ℚ) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hp : p ≤ 483*d) : ¬ 111960*d+R < 227*p := by linarith

theorem cycle_prevents_234 (p d R x0 x1 x2 x3 : ℚ)
    (hd : 0 ≤ d) (hR : 0 ≤ R)
    (h0 : p+x1 ≤ 252*d+x0) (h1 : p+x2 ≤ 480*d+x1)
    (h2 : p+x3 ≤ 600*d+x2) (h3 : p+x0 ≤ 600*d+x3) :
    ¬ 111960*d+R < 227*p :=
  no_234_criterion p d R hd hR (cycle_slope p d x0 x1 x2 x3 h0 h1 h2 h3)

theorem nonnegative_bonus_preserves_potential (p d w bonus u v : ℚ)
    (hd : 0 ≤ d) (hb : 0 ≤ bonus) (h : p+v ≤ d*w+u) :
    p+v ≤ d*(w+bonus)+u := by nlinarith

#print axioms cycle_counts_below_six
#print axioms cycle_weight_sum
#print axioms cycle_slope
#print axioms no_234_criterion
#print axioms cycle_prevents_234
#print axioms nonnegative_bonus_preserves_potential
end Snake9.UnsaturatedObstruction82
