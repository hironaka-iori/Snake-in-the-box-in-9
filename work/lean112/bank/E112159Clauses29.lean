import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1030 = false ∨ valuationOf q 1038 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1030)) (literal (valuationOf q) (1038)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 3 (meaning1030 q) (meaning1038 q) hs
  change valuationOf q 1030 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1030 = false ∨ valuation q 1038 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1031 = false ∨ valuationOf q 1039 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1031)) (literal (valuationOf q) (1039)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 4 (meaning1031 q) (meaning1039 q) hs
  change valuationOf q 1031 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1031 = false ∨ valuation q 1039 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1037 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1037)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 1 1 (meaning1005 q) (meaning1028 q) (meaning1037 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1028 = false ∨ valuation q 1037 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1038 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1038)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 1 2 (meaning1005 q) (meaning1029 q) (meaning1038 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1029 = false ∨ valuation q 1038 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1039 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1030)) (literal (valuationOf q) (1039)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 1 3 (meaning1005 q) (meaning1030 q) (meaning1039 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1030 = false ∨ valuation q 1039 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1031 = false ∨ valuationOf q 1040 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1031)) (literal (valuationOf q) (1040)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 1 4 (meaning1005 q) (meaning1031 q) (meaning1040 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1031 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1031 = false ∨ valuation q 1040 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1037 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1006)) (literal (valuationOf q) (1037)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 2 (meaning1006 q) (meaning1037 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1037 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1038 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1038)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 2 1 (meaning1006 q) (meaning1028 q) (meaning1038 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1028 = false ∨ valuation q 1038 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1039 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1039)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 2 2 (meaning1006 q) (meaning1029 q) (meaning1039 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1029 = false ∨ valuation q 1039 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1040 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1030)) (literal (valuationOf q) (1040)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 2 3 (meaning1006 q) (meaning1030 q) (meaning1040 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1030 = false ∨ valuation q 1040 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1031 = false ∨ valuationOf q 1041 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1031)) (literal (valuationOf q) (1041)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 2 4 (meaning1006 q) (meaning1031 q) (meaning1041 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1031 = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1031 = false ∨ valuation q 1041 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1042 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1042)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 2 5 (meaning1006 q) (meaning1032 q) (meaning1042 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1042 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1032 = false ∨ valuation q 1042 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1007 = false ∨ valuationOf q 1038 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1007)) (literal (valuationOf q) (1038)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 3 (meaning1007 q) (meaning1038 q) hs
  change valuationOf q 1007 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1007 = false ∨ valuation q 1038 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1007 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1039 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1007)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1039)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 3 1 (meaning1007 q) (meaning1028 q) (meaning1039 q) hs
  change valuationOf q 1007 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1007 = false ∨ valuation q 1028 = false ∨ valuation q 1039 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1007 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1040 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1007)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1040)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 3 2 (meaning1007 q) (meaning1029 q) (meaning1040 q) hs
  change valuationOf q 1007 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1007 = false ∨ valuation q 1029 = false ∨ valuation q 1040 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1007 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1041 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1007)) (literal (valuationOf q) (1030)) (literal (valuationOf q) (1041)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 3 3 (meaning1007 q) (meaning1030 q) (meaning1041 q) hs
  change valuationOf q 1007 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1007 = false ∨ valuation q 1030 = false ∨ valuation q 1041 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1039 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1008)) (literal (valuationOf q) (1039)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 4 (meaning1008 q) (meaning1039 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1039 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1040 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1040)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 4 1 (meaning1008 q) (meaning1028 q) (meaning1040 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1028 = false ∨ valuation q 1040 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1041 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1041)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 4 2 (meaning1008 q) (meaning1029 q) (meaning1041 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1029 = false ∨ valuation q 1041 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1040 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1009)) (literal (valuationOf q) (1040)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 5 (meaning1009 q) (meaning1040 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1040 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1042 = true := by
  have hs : count1036 q = (countLit q [-88, -90, -94, -95, -98, -99, -101]) + (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94, -95, -98, -99, -101]) (l₂ := [-104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1009)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1042)) (countLit q [-88, -90, -94, -95, -98, -99, -101]) (countLit q [-104, -105, -106, -108, -111, -113, -115, -117]) (count1036 q) 5 2 (meaning1009 q) (meaning1029 q) (meaning1042 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1042 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1029 = false ∨ valuation q 1042 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1056 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1040)) (literal (valuationOf q) (1056)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 1 5 (meaning977 q) (meaning1040 q) (meaning1056 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1040 = false ∨ valuation q 1056 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1054 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1054)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 2 2 (meaning978 q) (meaning1037 q) (meaning1054 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1037 = false ∨ valuation q 1054 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1055 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1055)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 2 3 (meaning978 q) (meaning1038 q) (meaning1055 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1038 = false ∨ valuation q 1055 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1056 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1039)) (literal (valuationOf q) (1056)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 2 4 (meaning978 q) (meaning1039 q) (meaning1056 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1039 = false ∨ valuation q 1056 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1057 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1040)) (literal (valuationOf q) (1057)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 2 5 (meaning978 q) (meaning1040 q) (meaning1057 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1040 = false ∨ valuation q 1057 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1058 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1041)) (literal (valuationOf q) (1058)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 2 6 (meaning978 q) (meaning1041 q) (meaning1058 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1041 = false ∨ valuation q 1058 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1042 = false ∨ valuationOf q 1059 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1042)) (literal (valuationOf q) (1059)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 2 7 (meaning978 q) (meaning1042 q) (meaning1059 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1042 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1042 = false ∨ valuation q 1059 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1056 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1056)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 3 3 (meaning979 q) (meaning1038 q) (meaning1056 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1038 = false ∨ valuation q 1056 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1057 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1039)) (literal (valuationOf q) (1057)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 3 4 (meaning979 q) (meaning1039 q) (meaning1057 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1039 = false ∨ valuation q 1057 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1058 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1040)) (literal (valuationOf q) (1058)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 3 5 (meaning979 q) (meaning1040 q) (meaning1058 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1040 = false ∨ valuation q 1058 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1059 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1041)) (literal (valuationOf q) (1059)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 3 6 (meaning979 q) (meaning1041 q) (meaning1059 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1041 = false ∨ valuation q 1059 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E159.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112159
