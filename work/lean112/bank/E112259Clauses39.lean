import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1001 = true := by
  have hs : count1000 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-112)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1001)) (countLit q [-112]) (countLit q [-113]) (count1000 q) 1 1 (meaningNeg112 q) (meaningNeg113 q) (meaning1001 q) hs
  change (! (valuationOf q 112)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 1001 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1002 = true := by
  have hs : count1002 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_right (literal (valuationOf q) (-116)) (literal (valuationOf q) (1002)) (countLit q [-114]) (countLit q [-116]) (count1002 q) 1 (meaningNeg116 q) (meaning1002 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1002 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1002 = true := by
  have hs : count1002 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_left (literal (valuationOf q) (-114)) (literal (valuationOf q) (1002)) (countLit q [-114]) (countLit q [-116]) (count1002 q) 1 (meaningNeg114 q) (meaning1002 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1002 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1004 = true := by
  have hs : count1004 q = (countLit q [-112, -113]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -116])
  have hm := merge_left (literal (valuationOf q) (1000)) (literal (valuationOf q) (1004)) (countLit q [-112, -113]) (countLit q [-114, -116]) (count1004 q) 1 (meaning1000 q) (meaning1004 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1004 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1005 = true := by
  have hs : count1004 q = (countLit q [-112, -113]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -116])
  have hm := merge_two (literal (valuationOf q) (1000)) (literal (valuationOf q) (1002)) (literal (valuationOf q) (1005)) (countLit q [-112, -113]) (countLit q [-114, -116]) (count1004 q) 1 1 (meaning1000 q) (meaning1002 q) (meaning1005 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1002 = false ∨ valuation q 1005 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1005 = true := by
  have hs : count1004 q = (countLit q [-112, -113]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -116])
  have hm := merge_left (literal (valuationOf q) (1001)) (literal (valuationOf q) (1005)) (countLit q [-112, -113]) (countLit q [-114, -116]) (count1004 q) 2 (meaning1001 q) (meaning1005 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1005 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1006 = true := by
  have hs : count1004 q = (countLit q [-112, -113]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -116])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1002)) (literal (valuationOf q) (1006)) (countLit q [-112, -113]) (countLit q [-114, -116]) (count1004 q) 2 1 (meaning1001 q) (meaning1002 q) (meaning1006 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1002 = false ∨ valuation q 1006 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1009 = true := by
  have hs : count1008 q = (countLit q [-104, -108, -109, -110]) + (countLit q [-112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-104, -108, -109, -110]) (l₂ := [-112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (996)) (literal (valuationOf q) (1004)) (literal (valuationOf q) (1009)) (countLit q [-104, -108, -109, -110]) (countLit q [-112, -113, -114, -116]) (count1008 q) 1 1 (meaning996 q) (meaning1004 q) (meaning1009 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1004 = false ∨ valuation q 1009 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1010 = true := by
  have hs : count1008 q = (countLit q [-104, -108, -109, -110]) + (countLit q [-112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-104, -108, -109, -110]) (l₂ := [-112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (996)) (literal (valuationOf q) (1005)) (literal (valuationOf q) (1010)) (countLit q [-104, -108, -109, -110]) (countLit q [-112, -113, -114, -116]) (count1008 q) 1 2 (meaning996 q) (meaning1005 q) (meaning1010 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1005 = false ∨ valuation q 1010 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1010 = true := by
  have hs : count1008 q = (countLit q [-104, -108, -109, -110]) + (countLit q [-112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-104, -108, -109, -110]) (l₂ := [-112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (997)) (literal (valuationOf q) (1004)) (literal (valuationOf q) (1010)) (countLit q [-104, -108, -109, -110]) (countLit q [-112, -113, -114, -116]) (count1008 q) 2 1 (meaning997 q) (meaning1004 q) (meaning1010 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1004 = false ∨ valuation q 1010 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1011 = true := by
  have hs : count1008 q = (countLit q [-104, -108, -109, -110]) + (countLit q [-112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-104, -108, -109, -110]) (l₂ := [-112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (997)) (literal (valuationOf q) (1005)) (literal (valuationOf q) (1011)) (countLit q [-104, -108, -109, -110]) (countLit q [-112, -113, -114, -116]) (count1008 q) 2 2 (meaning997 q) (meaning1005 q) (meaning1011 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1005 = false ∨ valuation q 1011 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1006 = false ∨ valuationOf q 1012 = true := by
  have hs : count1008 q = (countLit q [-104, -108, -109, -110]) + (countLit q [-112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-104, -108, -109, -110]) (l₂ := [-112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (997)) (literal (valuationOf q) (1006)) (literal (valuationOf q) (1012)) (countLit q [-104, -108, -109, -110]) (countLit q [-112, -113, -114, -116]) (count1008 q) 2 3 (meaning997 q) (meaning1006 q) (meaning1012 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1006 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1006 = false ∨ valuation q 1012 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1011 = true := by
  have hs : count1008 q = (countLit q [-104, -108, -109, -110]) + (countLit q [-112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-104, -108, -109, -110]) (l₂ := [-112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (998)) (literal (valuationOf q) (1004)) (literal (valuationOf q) (1011)) (countLit q [-104, -108, -109, -110]) (countLit q [-112, -113, -114, -116]) (count1008 q) 3 1 (meaning998 q) (meaning1004 q) (meaning1011 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 1004 = false ∨ valuation q 1011 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1017 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_right (literal (valuationOf q) (1009)) (literal (valuationOf q) (1017)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 2 (meaning1009 q) (meaning1017 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1017 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1010 = false ∨ valuationOf q 1018 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_right (literal (valuationOf q) (1010)) (literal (valuationOf q) (1018)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 3 (meaning1010 q) (meaning1018 q) hs
  change valuationOf q 1010 = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1010 = false ∨ valuation q 1018 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1011 = false ∨ valuationOf q 1019 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_right (literal (valuationOf q) (1011)) (literal (valuationOf q) (1019)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 4 (meaning1011 q) (meaning1019 q) hs
  change valuationOf q 1011 = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1011 = false ∨ valuation q 1019 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1018 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (1009)) (literal (valuationOf q) (1018)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 1 2 (meaning985 q) (meaning1009 q) (meaning1018 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 1009 = false ∨ valuation q 1018 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1019 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1019)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 1 3 (meaning985 q) (meaning1010 q) (meaning1019 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 1010 = false ∨ valuation q 1019 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1020 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1020)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 1 4 (meaning985 q) (meaning1011 q) (meaning1020 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 1011 = false ∨ valuation q 1020 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 1012 = false ∨ valuationOf q 1021 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (1012)) (literal (valuationOf q) (1021)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 1 5 (meaning985 q) (meaning1012 q) (meaning1021 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 1012 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 1012 = false ∨ valuation q 1021 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1019 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (986)) (literal (valuationOf q) (1009)) (literal (valuationOf q) (1019)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 2 2 (meaning986 q) (meaning1009 q) (meaning1019 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 1009 = false ∨ valuation q 1019 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1020 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (986)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1020)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 2 3 (meaning986 q) (meaning1010 q) (meaning1020 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 1010 = false ∨ valuation q 1020 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1021 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (986)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1021)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 2 4 (meaning986 q) (meaning1011 q) (meaning1021 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 1011 = false ∨ valuation q 1021 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 987 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1021 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (987)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1021)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 3 3 (meaning987 q) (meaning1010 q) (meaning1021 q) hs
  change valuationOf q 987 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 987 = false ∨ valuation q 1010 = false ∨ valuation q 1021 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 987 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1022 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (987)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1022)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 3 4 (meaning987 q) (meaning1011 q) (meaning1022 q) hs
  change valuationOf q 987 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 987 = false ∨ valuation q 1011 = false ∨ valuation q 1022 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1021 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (988)) (literal (valuationOf q) (1009)) (literal (valuationOf q) (1021)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 4 2 (meaning988 q) (meaning1009 q) (meaning1021 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 1009 = false ∨ valuation q 1021 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1022 = true := by
  have hs : count1016 q = (countLit q [-89, -91, -94, -95, -97, -99, -101]) + (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94, -95, -97, -99, -101]) (l₂ := [-104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (988)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1022)) (countLit q [-89, -91, -94, -95, -97, -99, -101]) (countLit q [-104, -108, -109, -110, -112, -113, -114, -116]) (count1016 q) 4 3 (meaning988 q) (meaning1010 q) (meaning1022 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 1010 = false ∨ valuation q 1022 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1035 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) + (countLit q [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) (l₂ := [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1035)) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) (countLit q [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1031 q) 2 3 (meaning959 q) (meaning1018 q) (meaning1035 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 1018 = false ∨ valuation q 1035 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1036 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) + (countLit q [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) (l₂ := [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1036)) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) (countLit q [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1031 q) 2 4 (meaning959 q) (meaning1019 q) (meaning1036 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 1019 = false ∨ valuation q 1036 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1037 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) + (countLit q [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) (l₂ := [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1037)) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) (countLit q [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1031 q) 2 5 (meaning959 q) (meaning1020 q) (meaning1037 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 1020 = false ∨ valuation q 1037 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1038 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) + (countLit q [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) (l₂ := [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1038)) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) (countLit q [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1031 q) 2 6 (meaning959 q) (meaning1021 q) (meaning1038 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 1021 = false ∨ valuation q 1038 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1039 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) + (countLit q [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) (l₂ := [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1039)) (countLit q [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]) (countLit q [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]) (count1031 q) 2 7 (meaning959 q) (meaning1022 q) (meaning1039 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 1022 = false ∨ valuation q 1039 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E259.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112259
