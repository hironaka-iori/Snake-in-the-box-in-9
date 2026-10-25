import SumWindow501
import CommonBudget
import Mathlib.Tactic
namespace Snake9.TripleReturnBudget
open Snake9.LocalWindow
set_option maxHeartbeats 0

def clipped (a : Nat) := min 6 a
def excess (a : Nat) := a - clipped a

theorem decomposition (a : Nat) : clipped a + excess a = a := by
  simp only [excess, clipped]
  have h := Nat.min_le_right 6 a
  omega

theorem triple_demand (a b c : Nat) (h : 13 ≤ a+b+c) :
    13-(clipped a+clipped b+clipped c) ≤ excess a+excess b+excess c := by
  have ha := decomposition a
  have hb := decomposition b
  have hc := decomposition c
  omega

theorem clipped_exact (a : Nat) (h : clipped a < 6) : clipped a = a := by
  unfold clipped at *
  omega

theorem exact_exclusion (a b c : Nat) (h : 13 ≤ a+b+c)
    (ha : clipped a < 6) (hb : clipped b < 6) (hc : clipped c < 6) :
    13 ≤ clipped a+clipped b+clipped c := by
  rw [clipped_exact a ha,clipped_exact b hb,clipped_exact c hc]
  exact h

theorem forward_subset (delta : Nat → Nat) (r s : Nat) (hs : s ≤ 2) :
    delta (r+s+1)+delta (r+s+4)+delta (r+s+5) ≤
      ∑ j ∈ Finset.range 7, delta (r+j+1) := by
  interval_cases s <;> simp [Finset.sum_range_succ, Nat.add_assoc] <;> omega

theorem reverse_subset (delta : Nat → Nat) (r s : Nat) (hs : s ≤ 2) :
    delta (r+s+5)+delta (r+s+2)+delta (r+s+1) ≤
      ∑ j ∈ Finset.range 7, delta (r+j+1) := by
  interval_cases s <;> simp [Finset.sum_range_succ, Nat.add_assoc] <;> omega

theorem snake_demand {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,a] : List Nat).getD j 0) :
    13-(clipped (coreAlpha p (r+1))+clipped (coreAlpha p (r+4))+clipped (coreAlpha p (r+5))) ≤
      excess (coreAlpha p (r+1))+excess (coreAlpha p (r+4))+excess (coreAlpha p (r+5)) :=
  triple_demand _ _ _ (JointIntervening501.low_count_sum p r a b c d e hn h9 hr hd)

theorem sparse_fours_excluded {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,a] : List Nat).getD j 0)
    (h1 : coreAlpha p (r+1) ≤ 4) (h4 : coreAlpha p (r+4) ≤ 4)
    (h5 : coreAlpha p (r+5) ≤ 4) : False := by
  have h := JointIntervening501.low_count_sum p r a b c d e hn h9 hr hd
  omega

#print axioms decomposition
#print axioms triple_demand
#print axioms clipped_exact
#print axioms exact_exclusion
#print axioms forward_subset
#print axioms reverse_subset
#print axioms snake_demand
#print axioms sparse_fours_excluded
#print axioms SixCountStateBudget.seven_window_budget
#print axioms SixCountStateBudget.maximum_demand
end Snake9.TripleReturnBudget
