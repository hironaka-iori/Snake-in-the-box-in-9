import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 985 = true := by
  have hs : count985 q = (countLit q [-89, -91, -93]) + (countLit q [-95, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -93]) (l₂ := [-95, -99, -101, -102])
  have hm := merge_left (literal (valuationOf q) (974)) (literal (valuationOf q) (985)) (countLit q [-89, -91, -93]) (countLit q [-95, -99, -101, -102]) (count985 q) 1 (meaning974 q) (meaning985 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 985 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 981 = false ∨ valuationOf q 986 = true := by
  have hs : count985 q = (countLit q [-89, -91, -93]) + (countLit q [-95, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -93]) (l₂ := [-95, -99, -101, -102])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (981)) (literal (valuationOf q) (986)) (countLit q [-89, -91, -93]) (countLit q [-95, -99, -101, -102]) (count985 q) 1 1 (meaning974 q) (meaning981 q) (meaning986 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 981 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 981 = false ∨ valuation q 986 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 982 = false ∨ valuationOf q 987 = true := by
  have hs : count985 q = (countLit q [-89, -91, -93]) + (countLit q [-95, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -93]) (l₂ := [-95, -99, -101, -102])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (982)) (literal (valuationOf q) (987)) (countLit q [-89, -91, -93]) (countLit q [-95, -99, -101, -102]) (count985 q) 1 2 (meaning974 q) (meaning982 q) (meaning987 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 982 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 982 = false ∨ valuation q 987 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 986 = true := by
  have hs : count985 q = (countLit q [-89, -91, -93]) + (countLit q [-95, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -93]) (l₂ := [-95, -99, -101, -102])
  have hm := merge_left (literal (valuationOf q) (975)) (literal (valuationOf q) (986)) (countLit q [-89, -91, -93]) (countLit q [-95, -99, -101, -102]) (count985 q) 2 (meaning975 q) (meaning986 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 986 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 981 = false ∨ valuationOf q 987 = true := by
  have hs : count985 q = (countLit q [-89, -91, -93]) + (countLit q [-95, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -93]) (l₂ := [-95, -99, -101, -102])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (981)) (literal (valuationOf q) (987)) (countLit q [-89, -91, -93]) (countLit q [-95, -99, -101, -102]) (count985 q) 2 1 (meaning975 q) (meaning981 q) (meaning987 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 981 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 981 = false ∨ valuation q 987 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 982 = false ∨ valuationOf q 988 = true := by
  have hs : count985 q = (countLit q [-89, -91, -93]) + (countLit q [-95, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -93]) (l₂ := [-95, -99, -101, -102])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (982)) (literal (valuationOf q) (988)) (countLit q [-89, -91, -93]) (countLit q [-95, -99, -101, -102]) (count985 q) 2 2 (meaning975 q) (meaning982 q) (meaning988 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 982 = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 982 = false ∨ valuation q 988 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 987 = true := by
  have hs : count985 q = (countLit q [-89, -91, -93]) + (countLit q [-95, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -93]) (l₂ := [-95, -99, -101, -102])
  have hm := merge_left (literal (valuationOf q) (976)) (literal (valuationOf q) (987)) (countLit q [-89, -91, -93]) (countLit q [-95, -99, -101, -102]) (count985 q) 3 (meaning976 q) (meaning987 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 987 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 981 = false ∨ valuationOf q 988 = true := by
  have hs : count985 q = (countLit q [-89, -91, -93]) + (countLit q [-95, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -93]) (l₂ := [-95, -99, -101, -102])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (981)) (literal (valuationOf q) (988)) (countLit q [-89, -91, -93]) (countLit q [-95, -99, -101, -102]) (count985 q) 3 1 (meaning976 q) (meaning981 q) (meaning988 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 981 = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 981 = false ∨ valuation q 988 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 992 = true := by
  have hs : count992 q = (countLit q [-105]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (992)) (countLit q [-105]) (countLit q [-107]) (count992 q) 1 (meaningNeg107 q) (meaning992 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 992 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 992 = true := by
  have hs : count992 q = (countLit q [-105]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-105)) (literal (valuationOf q) (992)) (countLit q [-105]) (countLit q [-107]) (count992 q) 1 (meaningNeg105 q) (meaning992 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 992 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 107 = true ∨ valuationOf q 993 = true := by
  have hs : count992 q = (countLit q [-105]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (993)) (countLit q [-105]) (countLit q [-107]) (count992 q) 1 1 (meaningNeg105 q) (meaningNeg107 q) (meaning993 q) hs
  change (! (valuationOf q 105)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 107 = true ∨ valuation q 993 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 994 = true := by
  have hs : count994 q = (countLit q [-108]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-109])
  have hm := merge_left (literal (valuationOf q) (-108)) (literal (valuationOf q) (994)) (countLit q [-108]) (countLit q [-109]) (count994 q) 1 (meaningNeg108 q) (meaning994 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 994 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 996 = true := by
  have hs : count996 q = (countLit q [-105, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -107]) (l₂ := [-108, -109])
  have hm := merge_right (literal (valuationOf q) (994)) (literal (valuationOf q) (996)) (countLit q [-105, -107]) (countLit q [-108, -109]) (count996 q) 1 (meaning994 q) (meaning996 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 996 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 996 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 994 = false ∨ valuationOf q 997 = true := by
  have hs : count996 q = (countLit q [-105, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -107]) (l₂ := [-108, -109])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (994)) (literal (valuationOf q) (997)) (countLit q [-105, -107]) (countLit q [-108, -109]) (count996 q) 1 1 (meaning992 q) (meaning994 q) (meaning997 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 994 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 994 = false ∨ valuation q 997 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 997 = true := by
  have hs : count996 q = (countLit q [-105, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -107]) (l₂ := [-108, -109])
  have hm := merge_left (literal (valuationOf q) (993)) (literal (valuationOf q) (997)) (countLit q [-105, -107]) (countLit q [-108, -109]) (count996 q) 2 (meaning993 q) (meaning997 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 997 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 994 = false ∨ valuationOf q 998 = true := by
  have hs : count996 q = (countLit q [-105, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -107]) (l₂ := [-108, -109])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (994)) (literal (valuationOf q) (998)) (countLit q [-105, -107]) (countLit q [-108, -109]) (count996 q) 2 1 (meaning993 q) (meaning994 q) (meaning998 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 994 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 994 = false ∨ valuation q 998 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1000 = true := by
  have hs : count1000 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_right (literal (valuationOf q) (-112)) (literal (valuationOf q) (1000)) (countLit q [-111]) (countLit q [-112]) (count1000 q) 1 (meaningNeg112 q) (meaning1000 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1000 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 112 = true ∨ valuationOf q 1001 = true := by
  have hs : count1000 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-112)) (literal (valuationOf q) (1001)) (countLit q [-111]) (countLit q [-112]) (count1000 q) 1 1 (meaningNeg111 q) (meaningNeg112 q) (meaning1001 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 112)) = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 1001 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1002 = true := by
  have hs : count1002 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (1002)) (countLit q [-113]) (countLit q [-114]) (count1002 q) 1 (meaningNeg114 q) (meaning1002 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1002 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1002 = true := by
  have hs : count1002 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_left (literal (valuationOf q) (-113)) (literal (valuationOf q) (1002)) (countLit q [-113]) (countLit q [-114]) (count1002 q) 1 (meaningNeg113 q) (meaning1002 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1002 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 114 = true ∨ valuationOf q 1003 = true := by
  have hs : count1002 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_two (literal (valuationOf q) (-113)) (literal (valuationOf q) (-114)) (literal (valuationOf q) (1003)) (countLit q [-113]) (countLit q [-114]) (count1002 q) 1 1 (meaningNeg113 q) (meaningNeg114 q) (meaning1003 q) hs
  change (! (valuationOf q 113)) = false ∨ (! (valuationOf q 114)) = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 1003 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1004 = true := by
  have hs : count1004 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_left (literal (valuationOf q) (1000)) (literal (valuationOf q) (1004)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count1004 q) 1 (meaning1000 q) (meaning1004 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1004 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1005 = true := by
  have hs : count1004 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1000)) (literal (valuationOf q) (1002)) (literal (valuationOf q) (1005)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count1004 q) 1 1 (meaning1000 q) (meaning1002 q) (meaning1005 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1002 = false ∨ valuation q 1005 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1005 = true := by
  have hs : count1004 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_left (literal (valuationOf q) (1001)) (literal (valuationOf q) (1005)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count1004 q) 2 (meaning1001 q) (meaning1005 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1005 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1006 = true := by
  have hs : count1004 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1002)) (literal (valuationOf q) (1006)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count1004 q) 2 1 (meaning1001 q) (meaning1002 q) (meaning1006 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1002 = false ∨ valuation q 1006 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1003 = false ∨ valuationOf q 1007 = true := by
  have hs : count1004 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1003)) (literal (valuationOf q) (1007)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count1004 q) 2 2 (meaning1001 q) (meaning1003 q) (meaning1007 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1003 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1003 = false ∨ valuation q 1007 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1009 = true := by
  have hs : count1008 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (996)) (literal (valuationOf q) (1004)) (literal (valuationOf q) (1009)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -113, -114]) (count1008 q) 1 1 (meaning996 q) (meaning1004 q) (meaning1009 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1004 = false ∨ valuation q 1009 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1010 = true := by
  have hs : count1008 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (996)) (literal (valuationOf q) (1005)) (literal (valuationOf q) (1010)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -113, -114]) (count1008 q) 1 2 (meaning996 q) (meaning1005 q) (meaning1010 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1005 = false ∨ valuation q 1010 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1006 = false ∨ valuationOf q 1011 = true := by
  have hs : count1008 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (996)) (literal (valuationOf q) (1006)) (literal (valuationOf q) (1011)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -113, -114]) (count1008 q) 1 3 (meaning996 q) (meaning1006 q) (meaning1011 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1006 = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1006 = false ∨ valuation q 1011 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1012 = true := by
  have hs : count1008 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (996)) (literal (valuationOf q) (1007)) (literal (valuationOf q) (1012)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -113, -114]) (count1008 q) 1 4 (meaning996 q) (meaning1007 q) (meaning1012 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1007 = false ∨ valuation q 1012 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1010 = true := by
  have hs : count1008 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (997)) (literal (valuationOf q) (1004)) (literal (valuationOf q) (1010)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -113, -114]) (count1008 q) 2 1 (meaning997 q) (meaning1004 q) (meaning1010 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1004 = false ∨ valuation q 1010 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1011 = true := by
  have hs : count1008 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (997)) (literal (valuationOf q) (1005)) (literal (valuationOf q) (1011)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -113, -114]) (count1008 q) 2 2 (meaning997 q) (meaning1005 q) (meaning1011 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1005 = false ∨ valuation q 1011 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E257.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112257
