import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-33, -36]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-33, -36]) (l₂ := [-37, -38])
  have hm := merge_right (literal (valuationOf q) (863)) (literal (valuationOf q) (865)) (countLit q [-33, -36]) (countLit q [-37, -38]) (count864 q) 2 (meaning863 q) (meaning865 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 865 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 862 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-33, -36]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-33, -36]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (860)) (literal (valuationOf q) (862)) (literal (valuationOf q) (865)) (countLit q [-33, -36]) (countLit q [-37, -38]) (count864 q) 1 1 (meaning860 q) (meaning862 q) (meaning865 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 862 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 862 = false ∨ valuation q 865 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 863 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-33, -36]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-33, -36]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (860)) (literal (valuationOf q) (863)) (literal (valuationOf q) (866)) (countLit q [-33, -36]) (countLit q [-37, -38]) (count864 q) 1 2 (meaning860 q) (meaning863 q) (meaning866 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 863 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 863 = false ∨ valuation q 866 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 863 = false ∨ valuationOf q 867 = true := by
  have hs : count864 q = (countLit q [-33, -36]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-33, -36]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (861)) (literal (valuationOf q) (863)) (literal (valuationOf q) (867)) (countLit q [-33, -36]) (countLit q [-37, -38]) (count864 q) 2 2 (meaning861 q) (meaning863 q) (meaning867 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 863 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 863 = false ∨ valuation q 867 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 866 = false ∨ valuationOf q 871 = true := by
  have hs : count868 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -36, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -36, -37, -38])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (866)) (literal (valuationOf q) (871)) (countLit q [-27, -29, -31]) (countLit q [-33, -36, -37, -38]) (count868 q) 1 3 (meaning857 q) (meaning866 q) (meaning871 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 866 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 866 = false ∨ valuation q 871 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 867 = false ∨ valuationOf q 872 = true := by
  have hs : count868 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -36, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -36, -37, -38])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (867)) (literal (valuationOf q) (872)) (countLit q [-27, -29, -31]) (countLit q [-33, -36, -37, -38]) (count868 q) 1 4 (meaning857 q) (meaning867 q) (meaning872 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 867 = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 867 = false ∨ valuation q 872 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 864 = false ∨ valuationOf q 870 = true := by
  have hs : count868 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -36, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -36, -37, -38])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (864)) (literal (valuationOf q) (870)) (countLit q [-27, -29, -31]) (countLit q [-33, -36, -37, -38]) (count868 q) 2 1 (meaning858 q) (meaning864 q) (meaning870 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 864 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 864 = false ∨ valuation q 870 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 865 = false ∨ valuationOf q 871 = true := by
  have hs : count868 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -36, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -36, -37, -38])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (865)) (literal (valuationOf q) (871)) (countLit q [-27, -29, -31]) (countLit q [-33, -36, -37, -38]) (count868 q) 2 2 (meaning858 q) (meaning865 q) (meaning871 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 865 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 865 = false ∨ valuation q 871 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (883)) (countLit q [-49]) (countLit q [-52]) (count883 q) 1 (meaningNeg52 q) (meaning883 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 883 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 52 = true ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (884)) (countLit q [-49]) (countLit q [-52]) (count883 q) 1 1 (meaningNeg49 q) (meaningNeg52 q) (meaning884 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 52 = true ∨ valuation q 884 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 885 = true := by
  have hs : count885 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (885)) (countLit q [-56]) (countLit q [-57]) (count885 q) 1 (meaningNeg57 q) (meaning885 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 885 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 885 = false ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-49, -52]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (885)) (literal (valuationOf q) (888)) (countLit q [-49, -52]) (countLit q [-56, -57]) (count887 q) 1 1 (meaning883 q) (meaning885 q) (meaning888 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 885 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 885 = false ∨ valuation q 888 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 885 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-49, -52]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (885)) (literal (valuationOf q) (889)) (countLit q [-49, -52]) (countLit q [-56, -57]) (count887 q) 2 1 (meaning884 q) (meaning885 q) (meaning889 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 885 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 885 = false ∨ valuation q 889 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 888 = false ∨ valuationOf q 892 = true := by
  have hs : count891 q = (countLit q [-40, -43, -46, -47]) + (countLit q [-49, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46, -47]) (l₂ := [-49, -52, -56, -57])
  have hm := merge_right (literal (valuationOf q) (888)) (literal (valuationOf q) (892)) (countLit q [-40, -43, -46, -47]) (countLit q [-49, -52, -56, -57]) (count891 q) 2 (meaning888 q) (meaning892 q) hs
  change valuationOf q 888 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 888 = false ∨ valuation q 892 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 893 = true := by
  have hs : count891 q = (countLit q [-40, -43, -46, -47]) + (countLit q [-49, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46, -47]) (l₂ := [-49, -52, -56, -57])
  have hm := merge_right (literal (valuationOf q) (889)) (literal (valuationOf q) (893)) (countLit q [-40, -43, -46, -47]) (countLit q [-49, -52, -56, -57]) (count891 q) 3 (meaning889 q) (meaning893 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 893 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 893 = false ∨ valuationOf q 904 = true := by
  have hs : count899 q = (countLit q [-27, -29, -31, -33, -36, -37, -38]) + (countLit q [-40, -43, -46, -47, -49, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -36, -37, -38]) (l₂ := [-40, -43, -46, -47, -49, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (893)) (literal (valuationOf q) (904)) (countLit q [-27, -29, -31, -33, -36, -37, -38]) (countLit q [-40, -43, -46, -47, -49, -52, -56, -57]) (count899 q) 3 3 (meaning870 q) (meaning893 q) (meaning904 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 893 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 893 = false ∨ valuation q 904 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 892 = false ∨ valuationOf q 904 = true := by
  have hs : count899 q = (countLit q [-27, -29, -31, -33, -36, -37, -38]) + (countLit q [-40, -43, -46, -47, -49, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -36, -37, -38]) (l₂ := [-40, -43, -46, -47, -49, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (892)) (literal (valuationOf q) (904)) (countLit q [-27, -29, -31, -33, -36, -37, -38]) (countLit q [-40, -43, -46, -47, -49, -52, -56, -57]) (count899 q) 4 2 (meaning871 q) (meaning892 q) (meaning904 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 892 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 892 = false ∨ valuation q 904 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 893 = false ∨ valuationOf q 905 = true := by
  have hs : count899 q = (countLit q [-27, -29, -31, -33, -36, -37, -38]) + (countLit q [-40, -43, -46, -47, -49, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -36, -37, -38]) (l₂ := [-40, -43, -46, -47, -49, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (893)) (literal (valuationOf q) (905)) (countLit q [-27, -29, -31, -33, -36, -37, -38]) (countLit q [-40, -43, -46, -47, -49, -52, -56, -57]) (count899 q) 4 3 (meaning871 q) (meaning893 q) (meaning905 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 893 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 893 = false ∨ valuation q 905 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 892 = false ∨ valuationOf q 905 = true := by
  have hs : count899 q = (countLit q [-27, -29, -31, -33, -36, -37, -38]) + (countLit q [-40, -43, -46, -47, -49, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -36, -37, -38]) (l₂ := [-40, -43, -46, -47, -49, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (892)) (literal (valuationOf q) (905)) (countLit q [-27, -29, -31, -33, -36, -37, -38]) (countLit q [-40, -43, -46, -47, -49, -52, -56, -57]) (count899 q) 5 2 (meaning872 q) (meaning892 q) (meaning905 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 892 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 892 = false ∨ valuation q 905 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 904 = false ∨ valuationOf q 923 = true := by
  have hs : count914 q = (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26]) + (countLit q [-27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26]) (l₂ := [-27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (904)) (literal (valuationOf q) (923)) (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26]) (countLit q [-27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) (count914 q) 4 6 (meaning844 q) (meaning904 q) (meaning923 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 904 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 904 = false ∨ valuation q 923 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 905 = false ∨ valuationOf q 924 = true := by
  have hs : count914 q = (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26]) + (countLit q [-27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26]) (l₂ := [-27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (905)) (literal (valuationOf q) (924)) (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26]) (countLit q [-27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) (count914 q) 4 7 (meaning844 q) (meaning905 q) (meaning924 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 905 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 905 = false ∨ valuation q 924 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 904 = false ∨ valuationOf q 925 = true := by
  have hs : count914 q = (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26]) + (countLit q [-27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26]) (l₂ := [-27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (904)) (literal (valuationOf q) (925)) (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26]) (countLit q [-27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) (count914 q) 6 6 (meaning846 q) (meaning904 q) (meaning925 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 904 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 904 = false ∨ valuation q 925 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 905 = false ∨ valuationOf q 926 = true := by
  have hs : count914 q = (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26]) + (countLit q [-27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26]) (l₂ := [-27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (905)) (literal (valuationOf q) (926)) (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26]) (countLit q [-27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) (count914 q) 6 7 (meaning846 q) (meaning905 q) (meaning926 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 905 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 905 = false ∨ valuation q 926 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 933 = true := by
  have hs : count933 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (933)) (countLit q [-62]) (countLit q [-64]) (count933 q) 1 (meaningNeg64 q) (meaning933 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 933 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 935 = true := by
  have hs : count935 q = (countLit q [-60]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62, -64])
  have hm := merge_right (literal (valuationOf q) (933)) (literal (valuationOf q) (935)) (countLit q [-60]) (countLit q [-62, -64]) (count935 q) 1 (meaning933 q) (meaning935 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 935 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (938)) (countLit q [-66]) (countLit q [-67]) (count938 q) 1 (meaningNeg66 q) (meaning938 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 938 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 940 = true := by
  have hs : count940 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (940)) (countLit q [-69]) (countLit q [-70]) (count940 q) 1 (meaningNeg70 q) (meaning940 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 940 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 942 = true := by
  have hs : count942 q = (countLit q [-66, -67]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-69, -70])
  have hm := merge_left (literal (valuationOf q) (938)) (literal (valuationOf q) (942)) (countLit q [-66, -67]) (countLit q [-69, -70]) (count942 q) 1 (meaning938 q) (meaning942 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 942 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 940 = false ∨ valuationOf q 943 = true := by
  have hs : count942 q = (countLit q [-66, -67]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-69, -70])
  have hm := merge_two (literal (valuationOf q) (938)) (literal (valuationOf q) (940)) (literal (valuationOf q) (943)) (countLit q [-66, -67]) (countLit q [-69, -70]) (count942 q) 1 1 (meaning938 q) (meaning940 q) (meaning943 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 940 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 940 = false ∨ valuation q 943 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 946 = true := by
  have hs : count946 q = (countLit q [-60, -62, -64]) + (countLit q [-66, -67, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -64]) (l₂ := [-66, -67, -69, -70])
  have hm := merge_right (literal (valuationOf q) (942)) (literal (valuationOf q) (946)) (countLit q [-60, -62, -64]) (countLit q [-66, -67, -69, -70]) (count946 q) 1 (meaning942 q) (meaning946 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 946 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 943 = false ∨ valuationOf q 948 = true := by
  have hs : count946 q = (countLit q [-60, -62, -64]) + (countLit q [-66, -67, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -64]) (l₂ := [-66, -67, -69, -70])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (943)) (literal (valuationOf q) (948)) (countLit q [-60, -62, -64]) (countLit q [-66, -67, -69, -70]) (count946 q) 1 2 (meaning935 q) (meaning943 q) (meaning948 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 943 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 943 = false ∨ valuation q 948 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-72]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-75])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (953)) (countLit q [-72]) (countLit q [-75]) (count953 q) 1 (meaningNeg72 q) (meaning953 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 953 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E158.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112158
