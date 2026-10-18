import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 807 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_right (literal (valuationOf q) (807)) (literal (valuationOf q) (811)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 2 (meaning807 q) (meaning811 q) hs
  change valuationOf q 807 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 807 = false ∨ valuation q 811 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 808 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_right (literal (valuationOf q) (808)) (literal (valuationOf q) (812)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 3 (meaning808 q) (meaning812 q) hs
  change valuationOf q 808 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 808 = false ∨ valuation q 812 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 810 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_left (literal (valuationOf q) (799)) (literal (valuationOf q) (810)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 1 (meaning799 q) (meaning810 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 810 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 806 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (799)) (literal (valuationOf q) (806)) (literal (valuationOf q) (811)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 1 1 (meaning799 q) (meaning806 q) (meaning811 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 806 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 806 = false ∨ valuation q 811 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 807 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (799)) (literal (valuationOf q) (807)) (literal (valuationOf q) (812)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 1 2 (meaning799 q) (meaning807 q) (meaning812 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 807 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 807 = false ∨ valuation q 812 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 808 = false ∨ valuationOf q 813 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (799)) (literal (valuationOf q) (808)) (literal (valuationOf q) (813)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 1 3 (meaning799 q) (meaning808 q) (meaning813 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 808 = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 808 = false ∨ valuation q 813 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 809 = false ∨ valuationOf q 814 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (799)) (literal (valuationOf q) (809)) (literal (valuationOf q) (814)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 1 4 (meaning799 q) (meaning809 q) (meaning814 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 809 = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 809 = false ∨ valuation q 814 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_left (literal (valuationOf q) (800)) (literal (valuationOf q) (811)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 2 (meaning800 q) (meaning811 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 811 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 806 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (806)) (literal (valuationOf q) (812)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 2 1 (meaning800 q) (meaning806 q) (meaning812 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 806 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 806 = false ∨ valuation q 812 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 807 = false ∨ valuationOf q 813 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (807)) (literal (valuationOf q) (813)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 2 2 (meaning800 q) (meaning807 q) (meaning813 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 807 = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 807 = false ∨ valuation q 813 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_left (literal (valuationOf q) (801)) (literal (valuationOf q) (812)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 3 (meaning801 q) (meaning812 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 812 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 806 = false ∨ valuationOf q 813 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (806)) (literal (valuationOf q) (813)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 3 1 (meaning801 q) (meaning806 q) (meaning813 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 806 = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 806 = false ∨ valuation q 813 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 817 = true := by
  have hs : count817 q = (countLit q [-17]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (817)) (countLit q [-17]) (countLit q [-20]) (count817 q) 1 (meaningNeg20 q) (meaning817 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 817 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 817 = true := by
  have hs : count817 q = (countLit q [-17]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (817)) (countLit q [-17]) (countLit q [-20]) (count817 q) 1 (meaningNeg17 q) (meaning817 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 817 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 20 = true ∨ valuationOf q 818 = true := by
  have hs : count817 q = (countLit q [-17]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (818)) (countLit q [-17]) (countLit q [-20]) (count817 q) 1 1 (meaningNeg17 q) (meaningNeg20 q) (meaning818 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 20 = true ∨ valuation q 818 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 819 = true := by
  have hs : count819 q = (countLit q [-16]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -20])
  have hm := merge_right (literal (valuationOf q) (817)) (literal (valuationOf q) (819)) (countLit q [-16]) (countLit q [-17, -20]) (count819 q) 1 (meaning817 q) (meaning819 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 819 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 818 = false ∨ valuationOf q 820 = true := by
  have hs : count819 q = (countLit q [-16]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -20])
  have hm := merge_right (literal (valuationOf q) (818)) (literal (valuationOf q) (820)) (countLit q [-16]) (countLit q [-17, -20]) (count819 q) 2 (meaning818 q) (meaning820 q) hs
  change valuationOf q 818 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 818 = false ∨ valuation q 820 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 819 = true := by
  have hs : count819 q = (countLit q [-16]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -20])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (819)) (countLit q [-16]) (countLit q [-17, -20]) (count819 q) 1 (meaningNeg16 q) (meaning819 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 819 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 817 = false ∨ valuationOf q 820 = true := by
  have hs : count819 q = (countLit q [-16]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -20])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (817)) (literal (valuationOf q) (820)) (countLit q [-16]) (countLit q [-17, -20]) (count819 q) 1 1 (meaningNeg16 q) (meaning817 q) (meaning820 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 817 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 817 = false ∨ valuation q 820 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 818 = false ∨ valuationOf q 821 = true := by
  have hs : count819 q = (countLit q [-16]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -20])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (818)) (literal (valuationOf q) (821)) (countLit q [-16]) (countLit q [-17, -20]) (count819 q) 1 2 (meaningNeg16 q) (meaning818 q) (meaning821 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 818 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 818 = false ∨ valuation q 821 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 822 = true := by
  have hs : count822 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (822)) (countLit q [-21]) (countLit q [-22]) (count822 q) 1 (meaningNeg22 q) (meaning822 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 822 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 822 = true := by
  have hs : count822 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (822)) (countLit q [-21]) (countLit q [-22]) (count822 q) 1 (meaningNeg21 q) (meaning822 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 822 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 22 = true ∨ valuationOf q 823 = true := by
  have hs : count822 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (823)) (countLit q [-21]) (countLit q [-22]) (count822 q) 1 1 (meaningNeg21 q) (meaningNeg22 q) (meaning823 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 22 = true ∨ valuation q 823 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 824 = true := by
  have hs : count824 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (824)) (countLit q [-24]) (countLit q [-25]) (count824 q) 1 (meaningNeg25 q) (meaning824 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 824 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 824 = true := by
  have hs : count824 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (824)) (countLit q [-24]) (countLit q [-25]) (count824 q) 1 (meaningNeg24 q) (meaning824 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 824 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 25 = true ∨ valuationOf q 825 = true := by
  have hs : count824 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (825)) (countLit q [-24]) (countLit q [-25]) (count824 q) 1 1 (meaningNeg24 q) (meaningNeg25 q) (meaning825 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 825 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 826 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_right (literal (valuationOf q) (824)) (literal (valuationOf q) (826)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 1 (meaning824 q) (meaning826 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 826 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_right (literal (valuationOf q) (825)) (literal (valuationOf q) (827)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 2 (meaning825 q) (meaning827 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 827 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 826 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_left (literal (valuationOf q) (822)) (literal (valuationOf q) (826)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 1 (meaning822 q) (meaning826 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 826 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 824 = false ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (824)) (literal (valuationOf q) (827)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 1 1 (meaning822 q) (meaning824 q) (meaning827 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 824 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 824 = false ∨ valuation q 827 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 825 = false ∨ valuationOf q 828 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (825)) (literal (valuationOf q) (828)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 1 2 (meaning822 q) (meaning825 q) (meaning828 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 825 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 825 = false ∨ valuation q 828 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_left (literal (valuationOf q) (823)) (literal (valuationOf q) (827)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 2 (meaning823 q) (meaning827 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 827 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E213.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112213
