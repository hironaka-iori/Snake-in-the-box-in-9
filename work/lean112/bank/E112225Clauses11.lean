import E112225Semantics
import B112E225Inputs
namespace Snake9.Regrowth.E112225
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1288)) (countLit q [-34]) (countLit q [-36]) (count1288 q) 1 (meaningNeg34 q) (meaning1288 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1288 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1290 = true := by
  have hs : count1290 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (1288)) (literal (valuationOf q) (1290)) (countLit q [-33]) (countLit q [-34, -36]) (count1290 q) 1 (meaning1288 q) (meaning1290 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1290 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1290 = true := by
  have hs : count1290 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1290)) (countLit q [-33]) (countLit q [-34, -36]) (count1290 q) 1 (meaningNeg33 q) (meaning1290 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1290 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1288 = false ∨ valuationOf q 1291 = true := by
  have hs : count1290 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1291)) (countLit q [-33]) (countLit q [-34, -36]) (count1290 q) 1 1 (meaningNeg33 q) (meaning1288 q) (meaning1291 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1288 = false ∨ valuation q 1291 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -34, -36])
  have hm := merge_right (literal (valuationOf q) (1290)) (literal (valuationOf q) (1293)) (countLit q [-27, -29, -31]) (countLit q [-33, -34, -36]) (count1293 q) 1 (meaning1290 q) (meaning1293 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1293 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -34, -36])
  have hm := merge_right (literal (valuationOf q) (1291)) (literal (valuationOf q) (1294)) (countLit q [-27, -29, -31]) (countLit q [-33, -34, -36]) (count1293 q) 2 (meaning1291 q) (meaning1294 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1294 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -34, -36])
  have hm := merge_left (literal (valuationOf q) (1285)) (literal (valuationOf q) (1293)) (countLit q [-27, -29, -31]) (countLit q [-33, -34, -36]) (count1293 q) 1 (meaning1285 q) (meaning1293 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1293 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -34, -36])
  have hm := merge_two (literal (valuationOf q) (1285)) (literal (valuationOf q) (1290)) (literal (valuationOf q) (1294)) (countLit q [-27, -29, -31]) (countLit q [-33, -34, -36]) (count1293 q) 1 1 (meaning1285 q) (meaning1290 q) (meaning1294 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1290 = false ∨ valuation q 1294 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 1286 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1295 = true := by
  have hs : count1293 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -34, -36])
  have hm := merge_two (literal (valuationOf q) (1286)) (literal (valuationOf q) (1290)) (literal (valuationOf q) (1295)) (countLit q [-27, -29, -31]) (countLit q [-33, -34, -36]) (count1293 q) 2 1 (meaning1286 q) (meaning1290 q) (meaning1295 q) hs
  change valuationOf q 1286 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 1286 = false ∨ valuation q 1290 = false ∨ valuation q 1295 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-40]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1299)) (countLit q [-40]) (countLit q [-43]) (count1299 q) 1 (meaningNeg40 q) (meaning1299 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1299 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 43 = true ∨ valuationOf q 1300 = true := by
  have hs : count1299 q = (countLit q [-40]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-43)) (literal (valuationOf q) (1300)) (countLit q [-40]) (countLit q [-43]) (count1299 q) 1 1 (meaningNeg40 q) (meaningNeg43 q) (meaning1300 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 43)) = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 43 = true ∨ valuation q 1300 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 1299 = false ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-39]) + (countLit q [-40, -43]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -43])
  have hm := merge_right (literal (valuationOf q) (1299)) (literal (valuationOf q) (1301)) (countLit q [-39]) (countLit q [-40, -43]) (count1301 q) 1 (meaning1299 q) (meaning1301 q) hs
  change valuationOf q 1299 = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 1299 = false ∨ valuation q 1301 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 1300 = false ∨ valuationOf q 1302 = true := by
  have hs : count1301 q = (countLit q [-39]) + (countLit q [-40, -43]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -43])
  have hm := merge_right (literal (valuationOf q) (1300)) (literal (valuationOf q) (1302)) (countLit q [-39]) (countLit q [-40, -43]) (count1301 q) 2 (meaning1300 q) (meaning1302 q) hs
  change valuationOf q 1300 = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 1300 = false ∨ valuation q 1302 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-39]) + (countLit q [-40, -43]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -43])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1301)) (countLit q [-39]) (countLit q [-40, -43]) (count1301 q) 1 (meaningNeg39 q) (meaning1301 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1301 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1299 = false ∨ valuationOf q 1302 = true := by
  have hs : count1301 q = (countLit q [-39]) + (countLit q [-40, -43]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -43])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (1299)) (literal (valuationOf q) (1302)) (countLit q [-39]) (countLit q [-40, -43]) (count1301 q) 1 1 (meaningNeg39 q) (meaning1299 q) (meaning1302 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1299 = false ∨ valuation q 1302 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1304 = true := by
  have hs : count1304 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1304)) (countLit q [-45]) (countLit q [-47]) (count1304 q) 1 (meaningNeg47 q) (meaning1304 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1304 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1304 = true := by
  have hs : count1304 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1304)) (countLit q [-45]) (countLit q [-47]) (count1304 q) 1 (meaningNeg45 q) (meaning1304 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1304 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (1306)) (countLit q [-49]) (countLit q [-50]) (count1306 q) 1 (meaningNeg50 q) (meaning1306 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1306 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1306)) (countLit q [-49]) (countLit q [-50]) (count1306 q) 1 (meaningNeg49 q) (meaning1306 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1306 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 1306 = false ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-45, -47]) + (countLit q [-49, -50]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -50])
  have hm := merge_right (literal (valuationOf q) (1306)) (literal (valuationOf q) (1308)) (countLit q [-45, -47]) (countLit q [-49, -50]) (count1308 q) 1 (meaning1306 q) (meaning1308 q) hs
  change valuationOf q 1306 = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 1306 = false ∨ valuation q 1308 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-45, -47]) + (countLit q [-49, -50]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -50])
  have hm := merge_left (literal (valuationOf q) (1304)) (literal (valuationOf q) (1308)) (countLit q [-45, -47]) (countLit q [-49, -50]) (count1308 q) 1 (meaning1304 q) (meaning1308 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1308 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1309 = true := by
  have hs : count1308 q = (countLit q [-45, -47]) + (countLit q [-49, -50]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -50])
  have hm := merge_two (literal (valuationOf q) (1304)) (literal (valuationOf q) (1306)) (literal (valuationOf q) (1309)) (countLit q [-45, -47]) (countLit q [-49, -50]) (count1308 q) 1 1 (meaning1304 q) (meaning1306 q) (meaning1309 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1306 = false ∨ valuation q 1309 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1312 = true := by
  have hs : count1312 q = (countLit q [-39, -40, -43]) + (countLit q [-45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -43]) (l₂ := [-45, -47, -49, -50])
  have hm := merge_right (literal (valuationOf q) (1308)) (literal (valuationOf q) (1312)) (countLit q [-39, -40, -43]) (countLit q [-45, -47, -49, -50]) (count1312 q) 1 (meaning1308 q) (meaning1312 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1312 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1312 = true := by
  have hs : count1312 q = (countLit q [-39, -40, -43]) + (countLit q [-45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -43]) (l₂ := [-45, -47, -49, -50])
  have hm := merge_left (literal (valuationOf q) (1301)) (literal (valuationOf q) (1312)) (countLit q [-39, -40, -43]) (countLit q [-45, -47, -49, -50]) (count1312 q) 1 (meaning1301 q) (meaning1312 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1312 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1313 = true := by
  have hs : count1312 q = (countLit q [-39, -40, -43]) + (countLit q [-45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -43]) (l₂ := [-45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1308)) (literal (valuationOf q) (1313)) (countLit q [-39, -40, -43]) (countLit q [-45, -47, -49, -50]) (count1312 q) 1 1 (meaning1301 q) (meaning1308 q) (meaning1313 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1308 = false ∨ valuation q 1313 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1309 = false ∨ valuationOf q 1314 = true := by
  have hs : count1312 q = (countLit q [-39, -40, -43]) + (countLit q [-45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -43]) (l₂ := [-45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1309)) (literal (valuationOf q) (1314)) (countLit q [-39, -40, -43]) (countLit q [-45, -47, -49, -50]) (count1312 q) 1 2 (meaning1301 q) (meaning1309 q) (meaning1314 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1309 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1309 = false ∨ valuation q 1314 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1314 = true := by
  have hs : count1312 q = (countLit q [-39, -40, -43]) + (countLit q [-45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -43]) (l₂ := [-45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1302)) (literal (valuationOf q) (1308)) (literal (valuationOf q) (1314)) (countLit q [-39, -40, -43]) (countLit q [-45, -47, -49, -50]) (count1312 q) 2 1 (meaning1302 q) (meaning1308 q) (meaning1314 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1308 = false ∨ valuation q 1314 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-27, -29, -31, -33, -34, -36]) + (countLit q [-39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -34, -36]) (l₂ := [-39, -40, -43, -45, -47, -49, -50])
  have hm := merge_right (literal (valuationOf q) (1312)) (literal (valuationOf q) (1319)) (countLit q [-27, -29, -31, -33, -34, -36]) (countLit q [-39, -40, -43, -45, -47, -49, -50]) (count1319 q) 1 (meaning1312 q) (meaning1319 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1319 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-27, -29, -31, -33, -34, -36]) + (countLit q [-39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -34, -36]) (l₂ := [-39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1320)) (countLit q [-27, -29, -31, -33, -34, -36]) (countLit q [-39, -40, -43, -45, -47, -49, -50]) (count1319 q) 1 1 (meaning1293 q) (meaning1312 q) (meaning1320 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1312 = false ∨ valuation q 1320 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1321 = true := by
  have hs : count1319 q = (countLit q [-27, -29, -31, -33, -34, -36]) + (countLit q [-39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -34, -36]) (l₂ := [-39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1321)) (countLit q [-27, -29, -31, -33, -34, -36]) (countLit q [-39, -40, -43, -45, -47, -49, -50]) (count1319 q) 1 2 (meaning1293 q) (meaning1313 q) (meaning1321 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1313 = false ∨ valuation q 1321 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1322 = true := by
  have hs : count1319 q = (countLit q [-27, -29, -31, -33, -34, -36]) + (countLit q [-39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -34, -36]) (l₂ := [-39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1322)) (countLit q [-27, -29, -31, -33, -34, -36]) (countLit q [-39, -40, -43, -45, -47, -49, -50]) (count1319 q) 1 3 (meaning1293 q) (meaning1314 q) (meaning1322 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1314 = false ∨ valuation q 1322 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1321 = true := by
  have hs : count1319 q = (countLit q [-27, -29, -31, -33, -34, -36]) + (countLit q [-39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -34, -36]) (l₂ := [-39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1294)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1321)) (countLit q [-27, -29, -31, -33, -34, -36]) (countLit q [-39, -40, -43, -45, -47, -49, -50]) (count1319 q) 2 1 (meaning1294 q) (meaning1312 q) (meaning1321 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1312 = false ∨ valuation q 1321 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E225.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112225
