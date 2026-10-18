import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 995 = false ∨ valuationOf q 999 = true := by
  have hs : count997 q = (countLit q [-97, -99]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-100, -101])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (995)) (literal (valuationOf q) (999)) (countLit q [-97, -99]) (countLit q [-100, -101]) (count997 q) 2 1 (meaning994 q) (meaning995 q) (meaning999 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 995 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 995 = false ∨ valuation q 999 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1000 = true := by
  have hs : count997 q = (countLit q [-97, -99]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-100, -101])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (996)) (literal (valuationOf q) (1000)) (countLit q [-97, -99]) (countLit q [-100, -101]) (count997 q) 2 2 (meaning994 q) (meaning996 q) (meaning1000 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 996 = false ∨ valuation q 1000 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-91, -93, -94]) + (countLit q [-97, -99, -100, -101]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94]) (l₂ := [-97, -99, -100, -101])
  have hm := merge_right (literal (valuationOf q) (997)) (literal (valuationOf q) (1001)) (countLit q [-91, -93, -94]) (countLit q [-97, -99, -100, -101]) (count1001 q) 1 (meaning997 q) (meaning1001 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1001 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-91, -93, -94]) + (countLit q [-97, -99, -100, -101]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94]) (l₂ := [-97, -99, -100, -101])
  have hm := merge_right (literal (valuationOf q) (998)) (literal (valuationOf q) (1002)) (countLit q [-91, -93, -94]) (countLit q [-97, -99, -100, -101]) (count1001 q) 2 (meaning998 q) (meaning1002 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 1002 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-91, -93, -94]) + (countLit q [-97, -99, -100, -101]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94]) (l₂ := [-97, -99, -100, -101])
  have hm := merge_right (literal (valuationOf q) (999)) (literal (valuationOf q) (1003)) (countLit q [-91, -93, -94]) (countLit q [-97, -99, -100, -101]) (count1001 q) 3 (meaning999 q) (meaning1003 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1003 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-91, -93, -94]) + (countLit q [-97, -99, -100, -101]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94]) (l₂ := [-97, -99, -100, -101])
  have hm := merge_right (literal (valuationOf q) (1000)) (literal (valuationOf q) (1004)) (countLit q [-91, -93, -94]) (countLit q [-97, -99, -100, -101]) (count1001 q) 4 (meaning1000 q) (meaning1004 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1004 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-91, -93, -94]) + (countLit q [-97, -99, -100, -101]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94]) (l₂ := [-97, -99, -100, -101])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1003)) (countLit q [-91, -93, -94]) (countLit q [-97, -99, -100, -101]) (count1001 q) 1 2 (meaning990 q) (meaning998 q) (meaning1003 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 998 = false ∨ valuation q 1003 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-91, -93, -94]) + (countLit q [-97, -99, -100, -101]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94]) (l₂ := [-97, -99, -100, -101])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1004)) (countLit q [-91, -93, -94]) (countLit q [-97, -99, -100, -101]) (count1001 q) 1 3 (meaning990 q) (meaning999 q) (meaning1004 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 999 = false ∨ valuation q 1004 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1005 = true := by
  have hs : count1001 q = (countLit q [-91, -93, -94]) + (countLit q [-97, -99, -100, -101]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94]) (l₂ := [-97, -99, -100, -101])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (1000)) (literal (valuationOf q) (1005)) (countLit q [-91, -93, -94]) (countLit q [-97, -99, -100, -101]) (count1001 q) 1 4 (meaning990 q) (meaning1000 q) (meaning1005 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 1000 = false ∨ valuation q 1005 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-91, -93, -94]) + (countLit q [-97, -99, -100, -101]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94]) (l₂ := [-97, -99, -100, -101])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1004)) (countLit q [-91, -93, -94]) (countLit q [-97, -99, -100, -101]) (count1001 q) 2 2 (meaning991 q) (meaning998 q) (meaning1004 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 998 = false ∨ valuation q 1004 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1005 = true := by
  have hs : count1001 q = (countLit q [-91, -93, -94]) + (countLit q [-97, -99, -100, -101]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94]) (l₂ := [-97, -99, -100, -101])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1005)) (countLit q [-91, -93, -94]) (countLit q [-97, -99, -100, -101]) (count1001 q) 2 3 (meaning991 q) (meaning999 q) (meaning1005 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 999 = false ∨ valuation q 1005 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1006 = true := by
  have hs : count1001 q = (countLit q [-91, -93, -94]) + (countLit q [-97, -99, -100, -101]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94]) (l₂ := [-97, -99, -100, -101])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1006)) (countLit q [-91, -93, -94]) (countLit q [-97, -99, -100, -101]) (count1001 q) 3 3 (meaning992 q) (meaning999 q) (meaning1006 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 999 = false ∨ valuation q 1006 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1008 = true := by
  have hs : count1008 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1008)) (countLit q [-103]) (countLit q [-104]) (count1008 q) 1 (meaningNeg103 q) (meaning1008 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1008 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1010 = true := by
  have hs : count1010 q = (countLit q [-105]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-105)) (literal (valuationOf q) (1010)) (countLit q [-105]) (countLit q [-108]) (count1010 q) 1 (meaningNeg105 q) (meaning1010 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1010 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-103, -104]) + (countLit q [-105, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-105, -108])
  have hm := merge_left (literal (valuationOf q) (1008)) (literal (valuationOf q) (1012)) (countLit q [-103, -104]) (countLit q [-105, -108]) (count1012 q) 1 (meaning1008 q) (meaning1012 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1012 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-103, -104]) + (countLit q [-105, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-105, -108])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1013)) (countLit q [-103, -104]) (countLit q [-105, -108]) (count1012 q) 1 1 (meaning1008 q) (meaning1010 q) (meaning1013 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1010 = false ∨ valuation q 1013 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-110]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1016)) (countLit q [-110]) (countLit q [-113]) (count1016 q) 1 (meaningNeg113 q) (meaning1016 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1016 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-110]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-110)) (literal (valuationOf q) (1016)) (countLit q [-110]) (countLit q [-113]) (count1016 q) 1 (meaningNeg110 q) (meaning1016 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1016 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1018 = true := by
  have hs : count1018 q = (countLit q [-116]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1018)) (countLit q [-116]) (countLit q [-117]) (count1018 q) 1 (meaningNeg117 q) (meaning1018 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1018 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1018 = true := by
  have hs : count1018 q = (countLit q [-116]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-116)) (literal (valuationOf q) (1018)) (countLit q [-116]) (countLit q [-117]) (count1018 q) 1 (meaningNeg116 q) (meaning1018 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1018 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1020 = true := by
  have hs : count1020 q = (countLit q [-110, -113]) + (countLit q [-116, -117]) := List.countP_append (p := literal q) (l₁ := [-110, -113]) (l₂ := [-116, -117])
  have hm := merge_left (literal (valuationOf q) (1016)) (literal (valuationOf q) (1020)) (countLit q [-110, -113]) (countLit q [-116, -117]) (count1020 q) 1 (meaning1016 q) (meaning1020 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1020 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1021 = true := by
  have hs : count1020 q = (countLit q [-110, -113]) + (countLit q [-116, -117]) := List.countP_append (p := literal q) (l₁ := [-110, -113]) (l₂ := [-116, -117])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1021)) (countLit q [-110, -113]) (countLit q [-116, -117]) (count1020 q) 1 1 (meaning1016 q) (meaning1018 q) (meaning1021 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1018 = false ∨ valuation q 1021 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1024 = true := by
  have hs : count1024 q = (countLit q [-103, -104, -105, -108]) + (countLit q [-110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -108]) (l₂ := [-110, -113, -116, -117])
  have hm := merge_left (literal (valuationOf q) (1012)) (literal (valuationOf q) (1024)) (countLit q [-103, -104, -105, -108]) (countLit q [-110, -113, -116, -117]) (count1024 q) 1 (meaning1012 q) (meaning1024 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1024 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-103, -104, -105, -108]) + (countLit q [-110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -108]) (l₂ := [-110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1025)) (countLit q [-103, -104, -105, -108]) (countLit q [-110, -113, -116, -117]) (count1024 q) 1 1 (meaning1012 q) (meaning1020 q) (meaning1025 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1020 = false ∨ valuation q 1025 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-103, -104, -105, -108]) + (countLit q [-110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -108]) (l₂ := [-110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1026)) (countLit q [-103, -104, -105, -108]) (countLit q [-110, -113, -116, -117]) (count1024 q) 1 2 (meaning1012 q) (meaning1021 q) (meaning1026 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1021 = false ∨ valuation q 1026 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-103, -104, -105, -108]) + (countLit q [-110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -105, -108]) (l₂ := [-110, -113, -116, -117])
  have hm := merge_left (literal (valuationOf q) (1013)) (literal (valuationOf q) (1025)) (countLit q [-103, -104, -105, -108]) (countLit q [-110, -113, -116, -117]) (count1024 q) 2 (meaning1013 q) (meaning1025 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1025 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1033 = true := by
  have hs : count1032 q = (countLit q [-91, -93, -94, -97, -99, -100, -101]) + (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -97, -99, -100, -101]) (l₂ := [-103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1033)) (countLit q [-91, -93, -94, -97, -99, -100, -101]) (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) (count1032 q) 1 1 (meaning1001 q) (meaning1024 q) (meaning1033 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1024 = false ∨ valuation q 1033 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-91, -93, -94, -97, -99, -100, -101]) + (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -97, -99, -100, -101]) (l₂ := [-103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1034)) (countLit q [-91, -93, -94, -97, -99, -100, -101]) (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) (count1032 q) 2 1 (meaning1002 q) (meaning1024 q) (meaning1034 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1024 = false ∨ valuation q 1034 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-91, -93, -94, -97, -99, -100, -101]) + (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -97, -99, -100, -101]) (l₂ := [-103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1036)) (countLit q [-91, -93, -94, -97, -99, -100, -101]) (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) (count1032 q) 2 3 (meaning1002 q) (meaning1026 q) (meaning1036 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1026 = false ∨ valuation q 1036 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-91, -93, -94, -97, -99, -100, -101]) + (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -97, -99, -100, -101]) (l₂ := [-103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1035)) (countLit q [-91, -93, -94, -97, -99, -100, -101]) (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) (count1032 q) 3 1 (meaning1003 q) (meaning1024 q) (meaning1035 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1024 = false ∨ valuation q 1035 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-91, -93, -94, -97, -99, -100, -101]) + (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -97, -99, -100, -101]) (l₂ := [-103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1036)) (countLit q [-91, -93, -94, -97, -99, -100, -101]) (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) (count1032 q) 3 2 (meaning1003 q) (meaning1025 q) (meaning1036 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1025 = false ∨ valuation q 1036 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-91, -93, -94, -97, -99, -100, -101]) + (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -97, -99, -100, -101]) (l₂ := [-103, -104, -105, -108, -110, -113, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1037)) (countLit q [-91, -93, -94, -97, -99, -100, -101]) (countLit q [-103, -104, -105, -108, -110, -113, -116, -117]) (count1032 q) 3 3 (meaning1003 q) (meaning1026 q) (meaning1037 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1026 = false ∨ valuation q 1037 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E213.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112213
