import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-87]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89, -92])
  have hm := merge_right (literal (valuationOf q) (988)) (literal (valuationOf q) (990)) (countLit q [-87]) (countLit q [-89, -92]) (count990 q) 1 (meaning988 q) (meaning990 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 990 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 989 = false ∨ valuationOf q 991 = true := by
  have hs : count990 q = (countLit q [-87]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89, -92])
  have hm := merge_right (literal (valuationOf q) (989)) (literal (valuationOf q) (991)) (countLit q [-87]) (countLit q [-89, -92]) (count990 q) 2 (meaning989 q) (meaning991 q) hs
  change valuationOf q 989 = false ∨ valuationOf q 991 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 989 = false ∨ valuation q 991 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-87]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89, -92])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (990)) (countLit q [-87]) (countLit q [-89, -92]) (count990 q) 1 (meaningNeg87 q) (meaning990 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 990 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 988 = false ∨ valuationOf q 991 = true := by
  have hs : count990 q = (countLit q [-87]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89, -92])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (988)) (literal (valuationOf q) (991)) (countLit q [-87]) (countLit q [-89, -92]) (count990 q) 1 1 (meaningNeg87 q) (meaning988 q) (meaning991 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 988 = false ∨ valuationOf q 991 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 988 = false ∨ valuation q 991 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 989 = false ∨ valuationOf q 992 = true := by
  have hs : count990 q = (countLit q [-87]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89, -92])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (989)) (literal (valuationOf q) (992)) (countLit q [-87]) (countLit q [-89, -92]) (count990 q) 1 2 (meaningNeg87 q) (meaning989 q) (meaning992 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 989 = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 989 = false ∨ valuation q 992 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 993 = true := by
  have hs : count993 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (993)) (countLit q [-95]) (countLit q [-96]) (count993 q) 1 (meaningNeg96 q) (meaning993 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 993 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 993 = true := by
  have hs : count993 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (993)) (countLit q [-95]) (countLit q [-96]) (count993 q) 1 (meaningNeg95 q) (meaning993 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 993 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 96 = true ∨ valuationOf q 994 = true := by
  have hs : count993 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (994)) (countLit q [-95]) (countLit q [-96]) (count993 q) 1 1 (meaningNeg95 q) (meaningNeg96 q) (meaning994 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 96 = true ∨ valuation q 994 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 995 = true := by
  have hs : count995 q = (countLit q [-97]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (995)) (countLit q [-97]) (countLit q [-102]) (count995 q) 1 (meaningNeg102 q) (meaning995 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 995 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 995 = true := by
  have hs : count995 q = (countLit q [-97]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (995)) (countLit q [-97]) (countLit q [-102]) (count995 q) 1 (meaningNeg97 q) (meaning995 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 995 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 102 = true ∨ valuationOf q 996 = true := by
  have hs : count995 q = (countLit q [-97]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-102])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-102)) (literal (valuationOf q) (996)) (countLit q [-97]) (countLit q [-102]) (count995 q) 1 1 (meaningNeg97 q) (meaningNeg102 q) (meaning996 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 102)) = false ∨ valuationOf q 996 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 102 = true ∨ valuation q 996 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 995 = false ∨ valuationOf q 997 = true := by
  have hs : count997 q = (countLit q [-95, -96]) + (countLit q [-97, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -102])
  have hm := merge_right (literal (valuationOf q) (995)) (literal (valuationOf q) (997)) (countLit q [-95, -96]) (countLit q [-97, -102]) (count997 q) 1 (meaning995 q) (meaning997 q) hs
  change valuationOf q 995 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 995 = false ∨ valuation q 997 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-95, -96]) + (countLit q [-97, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -102])
  have hm := merge_right (literal (valuationOf q) (996)) (literal (valuationOf q) (998)) (countLit q [-95, -96]) (countLit q [-97, -102]) (count997 q) 2 (meaning996 q) (meaning998 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 998 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 997 = true := by
  have hs : count997 q = (countLit q [-95, -96]) + (countLit q [-97, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -102])
  have hm := merge_left (literal (valuationOf q) (993)) (literal (valuationOf q) (997)) (countLit q [-95, -96]) (countLit q [-97, -102]) (count997 q) 1 (meaning993 q) (meaning997 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 997 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 995 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-95, -96]) + (countLit q [-97, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -102])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (995)) (literal (valuationOf q) (998)) (countLit q [-95, -96]) (countLit q [-97, -102]) (count997 q) 1 1 (meaning993 q) (meaning995 q) (meaning998 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 995 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 995 = false ∨ valuation q 998 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-95, -96]) + (countLit q [-97, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -102])
  have hm := merge_left (literal (valuationOf q) (994)) (literal (valuationOf q) (998)) (countLit q [-95, -96]) (countLit q [-97, -102]) (count997 q) 2 (meaning994 q) (meaning998 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 998 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 995 = false ∨ valuationOf q 999 = true := by
  have hs : count997 q = (countLit q [-95, -96]) + (countLit q [-97, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -102])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (995)) (literal (valuationOf q) (999)) (countLit q [-95, -96]) (countLit q [-97, -102]) (count997 q) 2 1 (meaning994 q) (meaning995 q) (meaning999 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 995 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 995 = false ∨ valuation q 999 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-87, -89, -92]) + (countLit q [-95, -96, -97, -102]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92]) (l₂ := [-95, -96, -97, -102])
  have hm := merge_right (literal (valuationOf q) (997)) (literal (valuationOf q) (1001)) (countLit q [-87, -89, -92]) (countLit q [-95, -96, -97, -102]) (count1001 q) 1 (meaning997 q) (meaning1001 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1001 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-87, -89, -92]) + (countLit q [-95, -96, -97, -102]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92]) (l₂ := [-95, -96, -97, -102])
  have hm := merge_right (literal (valuationOf q) (998)) (literal (valuationOf q) (1002)) (countLit q [-87, -89, -92]) (countLit q [-95, -96, -97, -102]) (count1001 q) 2 (meaning998 q) (meaning1002 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 1002 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-87, -89, -92]) + (countLit q [-95, -96, -97, -102]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92]) (l₂ := [-95, -96, -97, -102])
  have hm := merge_right (literal (valuationOf q) (999)) (literal (valuationOf q) (1003)) (countLit q [-87, -89, -92]) (countLit q [-95, -96, -97, -102]) (count1001 q) 3 (meaning999 q) (meaning1003 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1003 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-87, -89, -92]) + (countLit q [-95, -96, -97, -102]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92]) (l₂ := [-95, -96, -97, -102])
  have hm := merge_left (literal (valuationOf q) (990)) (literal (valuationOf q) (1001)) (countLit q [-87, -89, -92]) (countLit q [-95, -96, -97, -102]) (count1001 q) 1 (meaning990 q) (meaning1001 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 1001 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-87, -89, -92]) + (countLit q [-95, -96, -97, -102]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92]) (l₂ := [-95, -96, -97, -102])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1002)) (countLit q [-87, -89, -92]) (countLit q [-95, -96, -97, -102]) (count1001 q) 1 1 (meaning990 q) (meaning997 q) (meaning1002 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 997 = false ∨ valuation q 1002 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-87, -89, -92]) + (countLit q [-95, -96, -97, -102]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92]) (l₂ := [-95, -96, -97, -102])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1003)) (countLit q [-87, -89, -92]) (countLit q [-95, -96, -97, -102]) (count1001 q) 1 2 (meaning990 q) (meaning998 q) (meaning1003 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 998 = false ∨ valuation q 1003 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-87, -89, -92]) + (countLit q [-95, -96, -97, -102]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92]) (l₂ := [-95, -96, -97, -102])
  have hm := merge_left (literal (valuationOf q) (991)) (literal (valuationOf q) (1002)) (countLit q [-87, -89, -92]) (countLit q [-95, -96, -97, -102]) (count1001 q) 2 (meaning991 q) (meaning1002 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 1002 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-87, -89, -92]) + (countLit q [-95, -96, -97, -102]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92]) (l₂ := [-95, -96, -97, -102])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1003)) (countLit q [-87, -89, -92]) (countLit q [-95, -96, -97, -102]) (count1001 q) 2 1 (meaning991 q) (meaning997 q) (meaning1003 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 997 = false ∨ valuation q 1003 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-87, -89, -92]) + (countLit q [-95, -96, -97, -102]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92]) (l₂ := [-95, -96, -97, -102])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1004)) (countLit q [-87, -89, -92]) (countLit q [-95, -96, -97, -102]) (count1001 q) 2 2 (meaning991 q) (meaning998 q) (meaning1004 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 998 = false ∨ valuation q 1004 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-87, -89, -92]) + (countLit q [-95, -96, -97, -102]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92]) (l₂ := [-95, -96, -97, -102])
  have hm := merge_left (literal (valuationOf q) (992)) (literal (valuationOf q) (1003)) (countLit q [-87, -89, -92]) (countLit q [-95, -96, -97, -102]) (count1001 q) 3 (meaning992 q) (meaning1003 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 1003 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-87, -89, -92]) + (countLit q [-95, -96, -97, -102]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92]) (l₂ := [-95, -96, -97, -102])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1004)) (countLit q [-87, -89, -92]) (countLit q [-95, -96, -97, -102]) (count1001 q) 3 1 (meaning992 q) (meaning997 q) (meaning1004 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 997 = false ∨ valuation q 1004 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1005 = true := by
  have hs : count1001 q = (countLit q [-87, -89, -92]) + (countLit q [-95, -96, -97, -102]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -92]) (l₂ := [-95, -96, -97, -102])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1005)) (countLit q [-87, -89, -92]) (countLit q [-95, -96, -97, -102]) (count1001 q) 3 2 (meaning992 q) (meaning998 q) (meaning1005 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 998 = false ∨ valuation q 1005 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1008 = true := by
  have hs : count1008 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1008)) (countLit q [-103]) (countLit q [-104]) (count1008 q) 1 (meaningNeg103 q) (meaning1008 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1008 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1010 = true := by
  have hs : count1010 q = (countLit q [-106]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-109])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1010)) (countLit q [-106]) (countLit q [-109]) (count1010 q) 1 (meaningNeg106 q) (meaning1010 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1010 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1010 = false ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-103, -104]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-106, -109])
  have hm := merge_right (literal (valuationOf q) (1010)) (literal (valuationOf q) (1012)) (countLit q [-103, -104]) (countLit q [-106, -109]) (count1012 q) 1 (meaning1010 q) (meaning1012 q) hs
  change valuationOf q 1010 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1010 = false ∨ valuation q 1012 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E081.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112081
