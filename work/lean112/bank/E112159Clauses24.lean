import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 908 = false ∨ valuationOf q 928 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (908)) (literal (valuationOf q) (928)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 5 10 (meaning845 q) (meaning908 q) (meaning928 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 908 = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 908 = false ∨ valuation q 928 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 901 = false ∨ valuationOf q 922 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (901)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 6 3 (meaning846 q) (meaning901 q) (meaning922 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 901 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 901 = false ∨ valuation q 922 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 902 = false ∨ valuationOf q 923 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (902)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 6 4 (meaning846 q) (meaning902 q) (meaning923 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 902 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 902 = false ∨ valuation q 923 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 903 = false ∨ valuationOf q 924 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (903)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 6 5 (meaning846 q) (meaning903 q) (meaning924 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 903 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 903 = false ∨ valuation q 924 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 904 = false ∨ valuationOf q 925 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (904)) (literal (valuationOf q) (925)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 6 6 (meaning846 q) (meaning904 q) (meaning925 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 904 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 904 = false ∨ valuation q 925 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 905 = false ∨ valuationOf q 926 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (905)) (literal (valuationOf q) (926)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 6 7 (meaning846 q) (meaning905 q) (meaning926 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 905 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 905 = false ∨ valuation q 926 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 906 = false ∨ valuationOf q 927 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (906)) (literal (valuationOf q) (927)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 6 8 (meaning846 q) (meaning906 q) (meaning927 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 906 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 906 = false ∨ valuation q 927 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 901 = false ∨ valuationOf q 923 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (901)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 7 3 (meaning847 q) (meaning901 q) (meaning923 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 901 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 901 = false ∨ valuation q 923 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 902 = false ∨ valuationOf q 924 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (902)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 7 4 (meaning847 q) (meaning902 q) (meaning924 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 902 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 902 = false ∨ valuation q 924 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 903 = false ∨ valuationOf q 925 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (903)) (literal (valuationOf q) (925)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 7 5 (meaning847 q) (meaning903 q) (meaning925 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 903 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 903 = false ∨ valuation q 925 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 904 = false ∨ valuationOf q 926 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (904)) (literal (valuationOf q) (926)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 7 6 (meaning847 q) (meaning904 q) (meaning926 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 904 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 904 = false ∨ valuation q 926 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 905 = false ∨ valuationOf q 927 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (905)) (literal (valuationOf q) (927)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 7 7 (meaning847 q) (meaning905 q) (meaning927 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 905 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 905 = false ∨ valuation q 927 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 901 = false ∨ valuationOf q 924 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (901)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 8 3 (meaning848 q) (meaning901 q) (meaning924 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 901 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 901 = false ∨ valuation q 924 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 902 = false ∨ valuationOf q 925 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (902)) (literal (valuationOf q) (925)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 8 4 (meaning848 q) (meaning902 q) (meaning925 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 902 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 902 = false ∨ valuation q 925 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 903 = false ∨ valuationOf q 926 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (903)) (literal (valuationOf q) (926)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 8 5 (meaning848 q) (meaning903 q) (meaning926 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 903 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 903 = false ∨ valuation q 926 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 904 = false ∨ valuationOf q 927 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (904)) (literal (valuationOf q) (927)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 8 6 (meaning848 q) (meaning904 q) (meaning927 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 904 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 904 = false ∨ valuation q 927 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 901 = false ∨ valuationOf q 925 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (849)) (literal (valuationOf q) (901)) (literal (valuationOf q) (925)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 9 3 (meaning849 q) (meaning901 q) (meaning925 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 901 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 901 = false ∨ valuation q 925 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 903 = false ∨ valuationOf q 927 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (849)) (literal (valuationOf q) (903)) (literal (valuationOf q) (927)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 9 5 (meaning849 q) (meaning903 q) (meaning927 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 903 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 903 = false ∨ valuation q 927 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 933 = true := by
  have hs : count933 q = (countLit q [-60]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61])
  have hm := merge_right (literal (valuationOf q) (-61)) (literal (valuationOf q) (933)) (countLit q [-60]) (countLit q [-61]) (count933 q) 1 (meaningNeg61 q) (meaning933 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 933 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 933 = true := by
  have hs : count933 q = (countLit q [-60]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (933)) (countLit q [-60]) (countLit q [-61]) (count933 q) 1 (meaningNeg60 q) (meaning933 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 933 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 61 = true ∨ valuationOf q 934 = true := by
  have hs : count933 q = (countLit q [-60]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (-61)) (literal (valuationOf q) (934)) (countLit q [-60]) (countLit q [-61]) (count933 q) 1 1 (meaningNeg60 q) (meaningNeg61 q) (meaning934 q) hs
  change (! (valuationOf q 60)) = false ∨ (! (valuationOf q 61)) = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 61 = true ∨ valuation q 934 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 935 = true := by
  have hs : count935 q = (countLit q [-58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60, -61])
  have hm := merge_right (literal (valuationOf q) (933)) (literal (valuationOf q) (935)) (countLit q [-58]) (countLit q [-60, -61]) (count935 q) 1 (meaning933 q) (meaning935 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 935 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 936 = true := by
  have hs : count935 q = (countLit q [-58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60, -61])
  have hm := merge_right (literal (valuationOf q) (934)) (literal (valuationOf q) (936)) (countLit q [-58]) (countLit q [-60, -61]) (count935 q) 2 (meaning934 q) (meaning936 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 936 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 935 = true := by
  have hs : count935 q = (countLit q [-58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60, -61])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (935)) (countLit q [-58]) (countLit q [-60, -61]) (count935 q) 1 (meaningNeg58 q) (meaning935 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 935 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 933 = false ∨ valuationOf q 936 = true := by
  have hs : count935 q = (countLit q [-58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60, -61])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (933)) (literal (valuationOf q) (936)) (countLit q [-58]) (countLit q [-60, -61]) (count935 q) 1 1 (meaningNeg58 q) (meaning933 q) (meaning936 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 933 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 933 = false ∨ valuation q 936 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 934 = false ∨ valuationOf q 937 = true := by
  have hs : count935 q = (countLit q [-58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60, -61])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (934)) (literal (valuationOf q) (937)) (countLit q [-58]) (countLit q [-60, -61]) (count935 q) 1 2 (meaningNeg58 q) (meaning934 q) (meaning937 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 934 = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 934 = false ∨ valuation q 937 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (938)) (countLit q [-66]) (countLit q [-67]) (count938 q) 1 (meaningNeg67 q) (meaning938 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 938 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (938)) (countLit q [-66]) (countLit q [-67]) (count938 q) 1 (meaningNeg66 q) (meaning938 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 938 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 67 = true ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-66)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (939)) (countLit q [-66]) (countLit q [-67]) (count938 q) 1 1 (meaningNeg66 q) (meaningNeg67 q) (meaning939 q) hs
  change (! (valuationOf q 66)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 939 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 940 = true := by
  have hs : count940 q = (countLit q [-68]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (940)) (countLit q [-68]) (countLit q [-71]) (count940 q) 1 (meaningNeg71 q) (meaning940 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 940 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 940 = true := by
  have hs : count940 q = (countLit q [-68]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (940)) (countLit q [-68]) (countLit q [-71]) (count940 q) 1 (meaningNeg68 q) (meaning940 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 940 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 942 = true := by
  have hs : count942 q = (countLit q [-66, -67]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-68, -71])
  have hm := merge_right (literal (valuationOf q) (940)) (literal (valuationOf q) (942)) (countLit q [-66, -67]) (countLit q [-68, -71]) (count942 q) 1 (meaning940 q) (meaning942 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 942 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E159.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112159
