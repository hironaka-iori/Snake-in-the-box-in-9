import E112184Semantics
import B112E184Inputs
namespace Snake9.Regrowth.E112184
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause65 (q : Nat → Bool) : valuationOf q 1242 = false ∨ valuationOf q 1244 = true := by
  have hs : count1244 q = (countLit q [-31]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1242)) (literal (valuationOf q) (1244)) (countLit q [-31]) (countLit q [-34, -35]) (count1244 q) 1 (meaning1242 q) (meaning1244 q) hs
  change valuationOf q 1242 = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 1242 = false ∨ valuation q 1244 = true := counterClause65 (baseVal q)

theorem counterClause66 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1244 = true := by
  have hs : count1244 q = (countLit q [-31]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34, -35])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1244)) (countLit q [-31]) (countLit q [-34, -35]) (count1244 q) 1 (meaningNeg31 q) (meaning1244 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1244 = true := counterClause66 (baseVal q)

theorem counterClause67 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1247 = true := by
  have hs : count1247 q = (countLit q [-38]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1247)) (countLit q [-38]) (countLit q [-42]) (count1247 q) 1 (meaningNeg38 q) (meaning1247 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1247 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1247 = true := counterClause67 (baseVal q)

theorem counterClause68 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1249 = true := by
  have hs : count1249 q = (countLit q [-36]) + (countLit q [-38, -42]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38, -42])
  have hm := merge_right (literal (valuationOf q) (1247)) (literal (valuationOf q) (1249)) (countLit q [-36]) (countLit q [-38, -42]) (count1249 q) 1 (meaning1247 q) (meaning1249 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1249 = true := counterClause68 (baseVal q)

theorem counterClause69 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1249 = true := by
  have hs : count1249 q = (countLit q [-36]) + (countLit q [-38, -42]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38, -42])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1249)) (countLit q [-36]) (countLit q [-38, -42]) (count1249 q) 1 (meaningNeg36 q) (meaning1249 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1249 = true := counterClause69 (baseVal q)

theorem counterClause70 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1252 = true := by
  have hs : count1252 q = (countLit q [-31, -34, -35]) + (countLit q [-36, -38, -42]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-36, -38, -42])
  have hm := merge_right (literal (valuationOf q) (1249)) (literal (valuationOf q) (1252)) (countLit q [-31, -34, -35]) (countLit q [-36, -38, -42]) (count1252 q) 1 (meaning1249 q) (meaning1252 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1252 = true := counterClause70 (baseVal q)

theorem counterClause71 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1252 = true := by
  have hs : count1252 q = (countLit q [-31, -34, -35]) + (countLit q [-36, -38, -42]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-36, -38, -42])
  have hm := merge_left (literal (valuationOf q) (1244)) (literal (valuationOf q) (1252)) (countLit q [-31, -34, -35]) (countLit q [-36, -38, -42]) (count1252 q) 1 (meaning1244 q) (meaning1252 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1252 = true := counterClause71 (baseVal q)

theorem counterClause72 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1258 = true := by
  have hs : count1258 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1258)) (countLit q [-44]) (countLit q [-45]) (count1258 q) 1 (meaningNeg45 q) (meaning1258 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1258 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1258 = true := counterClause72 (baseVal q)

theorem counterClause73 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1258 = true := by
  have hs : count1258 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1258)) (countLit q [-44]) (countLit q [-45]) (count1258 q) 1 (meaningNeg44 q) (meaning1258 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1258 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1258 = true := counterClause73 (baseVal q)

theorem counterClause74 (q : Nat → Bool) : valuationOf q 1258 = false ∨ valuationOf q 1260 = true := by
  have hs : count1260 q = (countLit q [-43]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44, -45])
  have hm := merge_right (literal (valuationOf q) (1258)) (literal (valuationOf q) (1260)) (countLit q [-43]) (countLit q [-44, -45]) (count1260 q) 1 (meaning1258 q) (meaning1260 q) hs
  change valuationOf q 1258 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 1258 = false ∨ valuation q 1260 = true := counterClause74 (baseVal q)

theorem counterClause75 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1260 = true := by
  have hs : count1260 q = (countLit q [-43]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44, -45])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1260)) (countLit q [-43]) (countLit q [-44, -45]) (count1260 q) 1 (meaningNeg43 q) (meaning1260 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1260 = true := counterClause75 (baseVal q)

theorem counterClause76 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1263 = true := by
  have hs : count1263 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1263)) (countLit q [-51]) (countLit q [-52]) (count1263 q) 1 (meaningNeg52 q) (meaning1263 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1263 = true := counterClause76 (baseVal q)

theorem counterClause77 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1265 = true := by
  have hs : count1265 q = (countLit q [-49]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51, -52])
  have hm := merge_right (literal (valuationOf q) (1263)) (literal (valuationOf q) (1265)) (countLit q [-49]) (countLit q [-51, -52]) (count1265 q) 1 (meaning1263 q) (meaning1265 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1265 = true := counterClause77 (baseVal q)

theorem counterClause78 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1265 = true := by
  have hs : count1265 q = (countLit q [-49]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51, -52])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1265)) (countLit q [-49]) (countLit q [-51, -52]) (count1265 q) 1 (meaningNeg49 q) (meaning1265 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1265 = true := counterClause78 (baseVal q)

theorem counterClause79 (q : Nat → Bool) : valuationOf q 1260 = false ∨ valuationOf q 1268 = true := by
  have hs : count1268 q = (countLit q [-43, -44, -45]) + (countLit q [-49, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -45]) (l₂ := [-49, -51, -52])
  have hm := merge_left (literal (valuationOf q) (1260)) (literal (valuationOf q) (1268)) (countLit q [-43, -44, -45]) (countLit q [-49, -51, -52]) (count1268 q) 1 (meaning1260 q) (meaning1268 q) hs
  change valuationOf q 1260 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 1260 = false ∨ valuation q 1268 = true := counterClause79 (baseVal q)

theorem counterClause80 (q : Nat → Bool) : valuationOf q 1260 = false ∨ valuationOf q 1265 = false ∨ valuationOf q 1269 = true := by
  have hs : count1268 q = (countLit q [-43, -44, -45]) + (countLit q [-49, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -45]) (l₂ := [-49, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1260)) (literal (valuationOf q) (1265)) (literal (valuationOf q) (1269)) (countLit q [-43, -44, -45]) (countLit q [-49, -51, -52]) (count1268 q) 1 1 (meaning1260 q) (meaning1265 q) (meaning1269 q) hs
  change valuationOf q 1260 = false ∨ valuationOf q 1265 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 1260 = false ∨ valuation q 1265 = false ∨ valuation q 1269 = true := counterClause80 (baseVal q)

theorem counterClause81 (q : Nat → Bool) : valuationOf q 1268 = false ∨ valuationOf q 1274 = true := by
  have hs : count1274 q = (countLit q [-31, -34, -35, -36, -38, -42]) + (countLit q [-43, -44, -45, -49, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -38, -42]) (l₂ := [-43, -44, -45, -49, -51, -52])
  have hm := merge_right (literal (valuationOf q) (1268)) (literal (valuationOf q) (1274)) (countLit q [-31, -34, -35, -36, -38, -42]) (countLit q [-43, -44, -45, -49, -51, -52]) (count1274 q) 1 (meaning1268 q) (meaning1274 q) hs
  change valuationOf q 1268 = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 1268 = false ∨ valuation q 1274 = true := counterClause81 (baseVal q)

theorem counterClause82 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1275 = true := by
  have hs : count1274 q = (countLit q [-31, -34, -35, -36, -38, -42]) + (countLit q [-43, -44, -45, -49, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -38, -42]) (l₂ := [-43, -44, -45, -49, -51, -52])
  have hm := merge_right (literal (valuationOf q) (1269)) (literal (valuationOf q) (1275)) (countLit q [-31, -34, -35, -36, -38, -42]) (countLit q [-43, -44, -45, -49, -51, -52]) (count1274 q) 2 (meaning1269 q) (meaning1275 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1275 = true := counterClause82 (baseVal q)

theorem counterClause83 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1275 = true := by
  have hs : count1274 q = (countLit q [-31, -34, -35, -36, -38, -42]) + (countLit q [-43, -44, -45, -49, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -38, -42]) (l₂ := [-43, -44, -45, -49, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1252)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1275)) (countLit q [-31, -34, -35, -36, -38, -42]) (countLit q [-43, -44, -45, -49, -51, -52]) (count1274 q) 1 1 (meaning1252 q) (meaning1268 q) (meaning1275 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1268 = false ∨ valuation q 1275 = true := counterClause83 (baseVal q)

theorem counterClause84 (q : Nat → Bool) : valuationOf q 1234 = false ∨ valuationOf q 1274 = false ∨ valuationOf q 1283 = true := by
  have hs : count1282 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28]) + (countLit q [-31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28]) (l₂ := [-31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1234)) (literal (valuationOf q) (1274)) (literal (valuationOf q) (1283)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28]) (countLit q [-31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52]) (count1282 q) 1 1 (meaning1234 q) (meaning1274 q) (meaning1283 q) hs
  change valuationOf q 1234 = false ∨ valuationOf q 1274 = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 1234 = false ∨ valuation q 1274 = false ∨ valuation q 1283 = true := counterClause84 (baseVal q)

theorem counterClause85 (q : Nat → Bool) : valuationOf q 1234 = false ∨ valuationOf q 1275 = false ∨ valuationOf q 1284 = true := by
  have hs : count1282 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28]) + (countLit q [-31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28]) (l₂ := [-31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1234)) (literal (valuationOf q) (1275)) (literal (valuationOf q) (1284)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28]) (countLit q [-31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52]) (count1282 q) 1 2 (meaning1234 q) (meaning1275 q) (meaning1284 q) hs
  change valuationOf q 1234 = false ∨ valuationOf q 1275 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 1234 = false ∨ valuation q 1275 = false ∨ valuation q 1284 = true := counterClause85 (baseVal q)

theorem counterClause86 (q : Nat → Bool) : valuationOf q 1235 = false ∨ valuationOf q 1274 = false ∨ valuationOf q 1284 = true := by
  have hs : count1282 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28]) + (countLit q [-31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28]) (l₂ := [-31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1235)) (literal (valuationOf q) (1274)) (literal (valuationOf q) (1284)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28]) (countLit q [-31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52]) (count1282 q) 2 1 (meaning1235 q) (meaning1274 q) (meaning1284 q) hs
  change valuationOf q 1235 = false ∨ valuationOf q 1274 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 1235 = false ∨ valuation q 1274 = false ∨ valuation q 1284 = true := counterClause86 (baseVal q)

theorem counterClause87 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1290 = true := by
  have hs : count1290 q = (countLit q [-58]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (1290)) (countLit q [-58]) (countLit q [-59]) (count1290 q) 1 (meaningNeg59 q) (meaning1290 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1290 = true := counterClause87 (baseVal q)

theorem counterClause88 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1292 = true := by
  have hs : count1292 q = (countLit q [-54]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-58, -59])
  have hm := merge_right (literal (valuationOf q) (1290)) (literal (valuationOf q) (1292)) (countLit q [-54]) (countLit q [-58, -59]) (count1292 q) 1 (meaning1290 q) (meaning1292 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1292 = true := counterClause88 (baseVal q)

theorem counterClause89 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1295 = true := by
  have hs : count1295 q = (countLit q [-61]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-65])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1295)) (countLit q [-61]) (countLit q [-65]) (count1295 q) 1 (meaningNeg61 q) (meaning1295 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1295 = true := counterClause89 (baseVal q)

theorem counterClause90 (q : Nat → Bool) : valuationOf q 1295 = false ∨ valuationOf q 1297 = true := by
  have hs : count1297 q = (countLit q [-60]) + (countLit q [-61, -65]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -65])
  have hm := merge_right (literal (valuationOf q) (1295)) (literal (valuationOf q) (1297)) (countLit q [-60]) (countLit q [-61, -65]) (count1297 q) 1 (meaning1295 q) (meaning1297 q) hs
  change valuationOf q 1295 = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 1295 = false ∨ valuation q 1297 = true := counterClause90 (baseVal q)

theorem counterClause91 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1297 = true := by
  have hs : count1297 q = (countLit q [-60]) + (countLit q [-61, -65]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -65])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1297)) (countLit q [-60]) (countLit q [-61, -65]) (count1297 q) 1 (meaningNeg60 q) (meaning1297 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1297 = true := counterClause91 (baseVal q)

theorem counterClause92 (q : Nat → Bool) : valuationOf q 1297 = false ∨ valuationOf q 1300 = true := by
  have hs : count1300 q = (countLit q [-54, -58, -59]) + (countLit q [-60, -61, -65]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -59]) (l₂ := [-60, -61, -65])
  have hm := merge_right (literal (valuationOf q) (1297)) (literal (valuationOf q) (1300)) (countLit q [-54, -58, -59]) (countLit q [-60, -61, -65]) (count1300 q) 1 (meaning1297 q) (meaning1300 q) hs
  change valuationOf q 1297 = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 1297 = false ∨ valuation q 1300 = true := counterClause92 (baseVal q)

theorem counterClause93 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1300 = true := by
  have hs : count1300 q = (countLit q [-54, -58, -59]) + (countLit q [-60, -61, -65]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -59]) (l₂ := [-60, -61, -65])
  have hm := merge_left (literal (valuationOf q) (1292)) (literal (valuationOf q) (1300)) (countLit q [-54, -58, -59]) (countLit q [-60, -61, -65]) (count1300 q) 1 (meaning1292 q) (meaning1300 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1300 = true := counterClause93 (baseVal q)

theorem counterClause94 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1306)) (countLit q [-69]) (countLit q [-70]) (count1306 q) 1 (meaningNeg70 q) (meaning1306 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1306 = true := counterClause94 (baseVal q)

theorem counterClause95 (q : Nat → Bool) : valuationOf q 1306 = false ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-66]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-69, -70])
  have hm := merge_right (literal (valuationOf q) (1306)) (literal (valuationOf q) (1308)) (countLit q [-66]) (countLit q [-69, -70]) (count1308 q) 1 (meaning1306 q) (meaning1308 q) hs
  change valuationOf q 1306 = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 1306 = false ∨ valuation q 1308 = true := counterClause95 (baseVal q)

theorem counterClause96 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1311)) (countLit q [-74]) (countLit q [-76]) (count1311 q) 1 (meaningNeg76 q) (meaning1311 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1311 = true := counterClause96 (baseVal q)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E184.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112184
