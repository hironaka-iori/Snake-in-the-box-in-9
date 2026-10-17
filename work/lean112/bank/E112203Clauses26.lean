import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 851 = false ∨ valuationOf q 854 = true := by
  have hs : count853 q = (countLit q [-29]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-32, -33])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (851)) (literal (valuationOf q) (854)) (countLit q [-29]) (countLit q [-32, -33]) (count853 q) 1 1 (meaningNeg29 q) (meaning851 q) (meaning854 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 851 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 851 = false ∨ valuation q 854 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 852 = false ∨ valuationOf q 855 = true := by
  have hs : count853 q = (countLit q [-29]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-32, -33])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (852)) (literal (valuationOf q) (855)) (countLit q [-29]) (countLit q [-32, -33]) (count853 q) 1 2 (meaningNeg29 q) (meaning852 q) (meaning855 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 852 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 852 = false ∨ valuation q 855 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 856 = true := by
  have hs : count856 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (856)) (countLit q [-34]) (countLit q [-36]) (count856 q) 1 (meaningNeg36 q) (meaning856 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 856 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 36 = true ∨ valuationOf q 857 = true := by
  have hs : count856 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (857)) (countLit q [-34]) (countLit q [-36]) (count856 q) 1 1 (meaningNeg34 q) (meaningNeg36 q) (meaning857 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 857 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 858 = true := by
  have hs : count858 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (858)) (countLit q [-40]) (countLit q [-41]) (count858 q) 1 (meaningNeg41 q) (meaning858 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 858 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 858 = true := by
  have hs : count858 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (858)) (countLit q [-40]) (countLit q [-41]) (count858 q) 1 (meaningNeg40 q) (meaning858 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 858 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-34, -36]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-34, -36]) (l₂ := [-40, -41])
  have hm := merge_left (literal (valuationOf q) (856)) (literal (valuationOf q) (860)) (countLit q [-34, -36]) (countLit q [-40, -41]) (count860 q) 1 (meaning856 q) (meaning860 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 860 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 858 = false ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-34, -36]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-34, -36]) (l₂ := [-40, -41])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (858)) (literal (valuationOf q) (861)) (countLit q [-34, -36]) (countLit q [-40, -41]) (count860 q) 1 1 (meaning856 q) (meaning858 q) (meaning861 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 858 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 858 = false ∨ valuation q 861 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-34, -36]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-34, -36]) (l₂ := [-40, -41])
  have hm := merge_left (literal (valuationOf q) (857)) (literal (valuationOf q) (861)) (countLit q [-34, -36]) (countLit q [-40, -41]) (count860 q) 2 (meaning857 q) (meaning861 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 861 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 858 = false ∨ valuationOf q 862 = true := by
  have hs : count860 q = (countLit q [-34, -36]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-34, -36]) (l₂ := [-40, -41])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (858)) (literal (valuationOf q) (862)) (countLit q [-34, -36]) (countLit q [-40, -41]) (count860 q) 2 1 (meaning857 q) (meaning858 q) (meaning862 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 858 = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 858 = false ∨ valuation q 862 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 864 = true := by
  have hs : count864 q = (countLit q [-29, -32, -33]) + (countLit q [-34, -36, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-34, -36, -40, -41])
  have hm := merge_right (literal (valuationOf q) (860)) (literal (valuationOf q) (864)) (countLit q [-29, -32, -33]) (countLit q [-34, -36, -40, -41]) (count864 q) 1 (meaning860 q) (meaning864 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 864 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-29, -32, -33]) + (countLit q [-34, -36, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-34, -36, -40, -41])
  have hm := merge_right (literal (valuationOf q) (861)) (literal (valuationOf q) (865)) (countLit q [-29, -32, -33]) (countLit q [-34, -36, -40, -41]) (count864 q) 2 (meaning861 q) (meaning865 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 865 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 860 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-29, -32, -33]) + (countLit q [-34, -36, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-34, -36, -40, -41])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (860)) (literal (valuationOf q) (865)) (countLit q [-29, -32, -33]) (countLit q [-34, -36, -40, -41]) (count864 q) 1 1 (meaning853 q) (meaning860 q) (meaning865 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 860 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 860 = false ∨ valuation q 865 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 861 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-29, -32, -33]) + (countLit q [-34, -36, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-34, -36, -40, -41])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (861)) (literal (valuationOf q) (866)) (countLit q [-29, -32, -33]) (countLit q [-34, -36, -40, -41]) (count864 q) 1 2 (meaning853 q) (meaning861 q) (meaning866 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 861 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 861 = false ∨ valuation q 866 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 860 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-29, -32, -33]) + (countLit q [-34, -36, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-34, -36, -40, -41])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (860)) (literal (valuationOf q) (866)) (countLit q [-29, -32, -33]) (countLit q [-34, -36, -40, -41]) (count864 q) 2 1 (meaning854 q) (meaning860 q) (meaning866 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 860 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 860 = false ∨ valuation q 866 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 861 = false ∨ valuationOf q 867 = true := by
  have hs : count864 q = (countLit q [-29, -32, -33]) + (countLit q [-34, -36, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-34, -36, -40, -41])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (861)) (literal (valuationOf q) (867)) (countLit q [-29, -32, -33]) (countLit q [-34, -36, -40, -41]) (count864 q) 2 2 (meaning854 q) (meaning861 q) (meaning867 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 861 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 861 = false ∨ valuation q 867 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 862 = false ∨ valuationOf q 868 = true := by
  have hs : count864 q = (countLit q [-29, -32, -33]) + (countLit q [-34, -36, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-34, -36, -40, -41])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (862)) (literal (valuationOf q) (868)) (countLit q [-29, -32, -33]) (countLit q [-34, -36, -40, -41]) (count864 q) 2 3 (meaning854 q) (meaning862 q) (meaning868 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 862 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 862 = false ∨ valuation q 868 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 861 = false ∨ valuationOf q 868 = true := by
  have hs : count864 q = (countLit q [-29, -32, -33]) + (countLit q [-34, -36, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-34, -36, -40, -41])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (861)) (literal (valuationOf q) (868)) (countLit q [-29, -32, -33]) (countLit q [-34, -36, -40, -41]) (count864 q) 3 2 (meaning855 q) (meaning861 q) (meaning868 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 861 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 861 = false ∨ valuation q 868 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 44 = true ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (872)) (countLit q [-42]) (countLit q [-44]) (count871 q) 1 1 (meaningNeg42 q) (meaningNeg44 q) (meaning872 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 44 = true ∨ valuation q 872 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (873)) (countLit q [-46]) (countLit q [-47]) (count873 q) 1 (meaningNeg47 q) (meaning873 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 873 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (873)) (countLit q [-46]) (countLit q [-47]) (count873 q) 1 (meaningNeg46 q) (meaning873 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 873 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 47 = true ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (874)) (countLit q [-46]) (countLit q [-47]) (count873 q) 1 1 (meaningNeg46 q) (meaningNeg47 q) (meaning874 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 874 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-42, -44]) + (countLit q [-46, -47]) := List.countP_append (p := literal q) (l₁ := [-42, -44]) (l₂ := [-46, -47])
  have hm := merge_left (literal (valuationOf q) (872)) (literal (valuationOf q) (876)) (countLit q [-42, -44]) (countLit q [-46, -47]) (count875 q) 2 (meaning872 q) (meaning876 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 876 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 873 = false ∨ valuationOf q 877 = true := by
  have hs : count875 q = (countLit q [-42, -44]) + (countLit q [-46, -47]) := List.countP_append (p := literal q) (l₁ := [-42, -44]) (l₂ := [-46, -47])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (873)) (literal (valuationOf q) (877)) (countLit q [-42, -44]) (countLit q [-46, -47]) (count875 q) 2 1 (meaning872 q) (meaning873 q) (meaning877 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 873 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 873 = false ∨ valuation q 877 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 874 = false ∨ valuationOf q 878 = true := by
  have hs : count875 q = (countLit q [-42, -44]) + (countLit q [-46, -47]) := List.countP_append (p := literal q) (l₁ := [-42, -44]) (l₂ := [-46, -47])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (874)) (literal (valuationOf q) (878)) (countLit q [-42, -44]) (countLit q [-46, -47]) (count875 q) 2 2 (meaning872 q) (meaning874 q) (meaning878 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 874 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 874 = false ∨ valuation q 878 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (879)) (countLit q [-48]) (countLit q [-51]) (count879 q) 1 (meaningNeg51 q) (meaning879 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 879 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (879)) (countLit q [-48]) (countLit q [-51]) (count879 q) 1 (meaningNeg48 q) (meaning879 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 879 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 51 = true ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (880)) (countLit q [-48]) (countLit q [-51]) (count879 q) 1 1 (meaningNeg48 q) (meaningNeg51 q) (meaning880 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 51 = true ∨ valuation q 880 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (881)) (countLit q [-52]) (countLit q [-54]) (count881 q) 1 (meaningNeg54 q) (meaning881 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 881 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (881)) (countLit q [-52]) (countLit q [-54]) (count881 q) 1 (meaningNeg52 q) (meaning881 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 881 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 54 = true ∨ valuationOf q 882 = true := by
  have hs : count881 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (882)) (countLit q [-52]) (countLit q [-54]) (count881 q) 1 1 (meaningNeg52 q) (meaningNeg54 q) (meaning882 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 882 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-48, -51]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -51]) (l₂ := [-52, -54])
  have hm := merge_right (literal (valuationOf q) (881)) (literal (valuationOf q) (883)) (countLit q [-48, -51]) (countLit q [-52, -54]) (count883 q) 1 (meaning881 q) (meaning883 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 883 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E203.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112203
