import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1286 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-53, -54, -56]) + (countLit q [-59, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56]) (l₂ := [-59, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1280)) (literal (valuationOf q) (1286)) (literal (valuationOf q) (1290)) (countLit q [-53, -54, -56]) (countLit q [-59, -60, -62]) (count1288 q) 1 2 (meaning1280 q) (meaning1286 q) (meaning1290 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1286 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1286 = false ∨ valuation q 1290 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 1281 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-53, -54, -56]) + (countLit q [-59, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56]) (l₂ := [-59, -60, -62])
  have hm := merge_left (literal (valuationOf q) (1281)) (literal (valuationOf q) (1289)) (countLit q [-53, -54, -56]) (countLit q [-59, -60, -62]) (count1288 q) 2 (meaning1281 q) (meaning1289 q) hs
  change valuationOf q 1281 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 1281 = false ∨ valuation q 1289 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 1281 = false ∨ valuationOf q 1285 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-53, -54, -56]) + (countLit q [-59, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56]) (l₂ := [-59, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1281)) (literal (valuationOf q) (1285)) (literal (valuationOf q) (1290)) (countLit q [-53, -54, -56]) (countLit q [-59, -60, -62]) (count1288 q) 2 1 (meaning1281 q) (meaning1285 q) (meaning1290 q) hs
  change valuationOf q 1281 = false ∨ valuationOf q 1285 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 1281 = false ∨ valuation q 1285 = false ∨ valuation q 1290 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 1281 = false ∨ valuationOf q 1286 = false ∨ valuationOf q 1291 = true := by
  have hs : count1288 q = (countLit q [-53, -54, -56]) + (countLit q [-59, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56]) (l₂ := [-59, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1281)) (literal (valuationOf q) (1286)) (literal (valuationOf q) (1291)) (countLit q [-53, -54, -56]) (countLit q [-59, -60, -62]) (count1288 q) 2 2 (meaning1281 q) (meaning1286 q) (meaning1291 q) hs
  change valuationOf q 1281 = false ∨ valuationOf q 1286 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 1281 = false ∨ valuation q 1286 = false ∨ valuation q 1291 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1294 = true := by
  have hs : count1294 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1294)) (countLit q [-67]) (countLit q [-68]) (count1294 q) 1 (meaningNeg67 q) (meaning1294 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1294 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1296 = true := by
  have hs : count1296 q = (countLit q [-65]) + (countLit q [-67, -68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -68])
  have hm := merge_right (literal (valuationOf q) (1294)) (literal (valuationOf q) (1296)) (countLit q [-65]) (countLit q [-67, -68]) (count1296 q) 1 (meaning1294 q) (meaning1296 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1296 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1299)) (countLit q [-72]) (countLit q [-73]) (count1299 q) 1 (meaningNeg73 q) (meaning1299 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1299 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1299)) (countLit q [-72]) (countLit q [-73]) (count1299 q) 1 (meaningNeg72 q) (meaning1299 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1299 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1300 = true := by
  have hs : count1299 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1300)) (countLit q [-72]) (countLit q [-73]) (count1299 q) 1 1 (meaningNeg72 q) (meaningNeg73 q) (meaning1300 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 1300 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 1299 = false ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72, -73])
  have hm := merge_right (literal (valuationOf q) (1299)) (literal (valuationOf q) (1301)) (countLit q [-69]) (countLit q [-72, -73]) (count1301 q) 1 (meaning1299 q) (meaning1301 q) hs
  change valuationOf q 1299 = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 1299 = false ∨ valuation q 1301 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 1300 = false ∨ valuationOf q 1302 = true := by
  have hs : count1301 q = (countLit q [-69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72, -73])
  have hm := merge_right (literal (valuationOf q) (1300)) (literal (valuationOf q) (1302)) (countLit q [-69]) (countLit q [-72, -73]) (count1301 q) 2 (meaning1300 q) (meaning1302 q) hs
  change valuationOf q 1300 = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 1300 = false ∨ valuation q 1302 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1304 = true := by
  have hs : count1304 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1301)) (literal (valuationOf q) (1304)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73]) (count1304 q) 1 (meaning1301 q) (meaning1304 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1304 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1305 = true := by
  have hs : count1304 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1302)) (literal (valuationOf q) (1305)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73]) (count1304 q) 2 (meaning1302 q) (meaning1305 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1305 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1304 = true := by
  have hs : count1304 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73])
  have hm := merge_left (literal (valuationOf q) (1296)) (literal (valuationOf q) (1304)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73]) (count1304 q) 1 (meaning1296 q) (meaning1304 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1304 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1301 = false ∨ valuationOf q 1305 = true := by
  have hs : count1304 q = (countLit q [-65, -67, -68]) + (countLit q [-69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68]) (l₂ := [-69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1296)) (literal (valuationOf q) (1301)) (literal (valuationOf q) (1305)) (countLit q [-65, -67, -68]) (countLit q [-69, -72, -73]) (count1304 q) 1 1 (meaning1296 q) (meaning1301 q) (meaning1305 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1301 = false ∨ valuationOf q 1305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1301 = false ∨ valuation q 1305 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1310 = true := by
  have hs : count1310 q = (countLit q [-53, -54, -56, -59, -60, -62]) + (countLit q [-65, -67, -68, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62]) (l₂ := [-65, -67, -68, -69, -72, -73])
  have hm := merge_left (literal (valuationOf q) (1288)) (literal (valuationOf q) (1310)) (countLit q [-53, -54, -56, -59, -60, -62]) (countLit q [-65, -67, -68, -69, -72, -73]) (count1310 q) 1 (meaning1288 q) (meaning1310 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1310 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1311 = true := by
  have hs : count1310 q = (countLit q [-53, -54, -56, -59, -60, -62]) + (countLit q [-65, -67, -68, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62]) (l₂ := [-65, -67, -68, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1288)) (literal (valuationOf q) (1304)) (literal (valuationOf q) (1311)) (countLit q [-53, -54, -56, -59, -60, -62]) (countLit q [-65, -67, -68, -69, -72, -73]) (count1310 q) 1 1 (meaning1288 q) (meaning1304 q) (meaning1311 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1304 = false ∨ valuation q 1311 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1305 = false ∨ valuationOf q 1312 = true := by
  have hs : count1310 q = (countLit q [-53, -54, -56, -59, -60, -62]) + (countLit q [-65, -67, -68, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62]) (l₂ := [-65, -67, -68, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1288)) (literal (valuationOf q) (1305)) (literal (valuationOf q) (1312)) (countLit q [-53, -54, -56, -59, -60, -62]) (countLit q [-65, -67, -68, -69, -72, -73]) (count1310 q) 1 2 (meaning1288 q) (meaning1305 q) (meaning1312 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1305 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1305 = false ∨ valuation q 1312 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1311 = true := by
  have hs : count1310 q = (countLit q [-53, -54, -56, -59, -60, -62]) + (countLit q [-65, -67, -68, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62]) (l₂ := [-65, -67, -68, -69, -72, -73])
  have hm := merge_left (literal (valuationOf q) (1289)) (literal (valuationOf q) (1311)) (countLit q [-53, -54, -56, -59, -60, -62]) (countLit q [-65, -67, -68, -69, -72, -73]) (count1310 q) 2 (meaning1289 q) (meaning1311 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1311 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1312 = true := by
  have hs : count1310 q = (countLit q [-53, -54, -56, -59, -60, -62]) + (countLit q [-65, -67, -68, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62]) (l₂ := [-65, -67, -68, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1304)) (literal (valuationOf q) (1312)) (countLit q [-53, -54, -56, -59, -60, -62]) (countLit q [-65, -67, -68, -69, -72, -73]) (count1310 q) 2 1 (meaning1289 q) (meaning1304 q) (meaning1312 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1304 = false ∨ valuation q 1312 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1305 = false ∨ valuationOf q 1313 = true := by
  have hs : count1310 q = (countLit q [-53, -54, -56, -59, -60, -62]) + (countLit q [-65, -67, -68, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62]) (l₂ := [-65, -67, -68, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1305)) (literal (valuationOf q) (1313)) (countLit q [-53, -54, -56, -59, -60, -62]) (countLit q [-65, -67, -68, -69, -72, -73]) (count1310 q) 2 2 (meaning1289 q) (meaning1305 q) (meaning1313 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1305 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1305 = false ∨ valuation q 1313 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1312 = true := by
  have hs : count1310 q = (countLit q [-53, -54, -56, -59, -60, -62]) + (countLit q [-65, -67, -68, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62]) (l₂ := [-65, -67, -68, -69, -72, -73])
  have hm := merge_left (literal (valuationOf q) (1290)) (literal (valuationOf q) (1312)) (countLit q [-53, -54, -56, -59, -60, -62]) (countLit q [-65, -67, -68, -69, -72, -73]) (count1310 q) 3 (meaning1290 q) (meaning1312 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1312 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1313 = true := by
  have hs : count1310 q = (countLit q [-53, -54, -56, -59, -60, -62]) + (countLit q [-65, -67, -68, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62]) (l₂ := [-65, -67, -68, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1304)) (literal (valuationOf q) (1313)) (countLit q [-53, -54, -56, -59, -60, -62]) (countLit q [-65, -67, -68, -69, -72, -73]) (count1310 q) 3 1 (meaning1290 q) (meaning1304 q) (meaning1313 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1304 = false ∨ valuation q 1313 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1305 = false ∨ valuationOf q 1314 = true := by
  have hs : count1310 q = (countLit q [-53, -54, -56, -59, -60, -62]) + (countLit q [-65, -67, -68, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62]) (l₂ := [-65, -67, -68, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1305)) (literal (valuationOf q) (1314)) (countLit q [-53, -54, -56, -59, -60, -62]) (countLit q [-65, -67, -68, -69, -72, -73]) (count1310 q) 3 2 (meaning1290 q) (meaning1305 q) (meaning1314 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1305 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1305 = false ∨ valuation q 1314 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1314 = true := by
  have hs : count1310 q = (countLit q [-53, -54, -56, -59, -60, -62]) + (countLit q [-65, -67, -68, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62]) (l₂ := [-65, -67, -68, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1304)) (literal (valuationOf q) (1314)) (countLit q [-53, -54, -56, -59, -60, -62]) (countLit q [-65, -67, -68, -69, -72, -73]) (count1310 q) 4 1 (meaning1291 q) (meaning1304 q) (meaning1314 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1304 = false ∨ valuation q 1314 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1320 = true := by
  have hs : count1320 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1320)) (countLit q [-78]) (countLit q [-79]) (count1320 q) 1 (meaningNeg79 q) (meaning1320 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1320 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1320 = true := by
  have hs : count1320 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1320)) (countLit q [-78]) (countLit q [-79]) (count1320 q) 1 (meaningNeg78 q) (meaning1320 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1320 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1321 = true := by
  have hs : count1320 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1321)) (countLit q [-78]) (countLit q [-79]) (count1320 q) 1 1 (meaningNeg78 q) (meaningNeg79 q) (meaning1321 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 79 = true ∨ valuation q 1321 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-76]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (1320)) (literal (valuationOf q) (1322)) (countLit q [-76]) (countLit q [-78, -79]) (count1322 q) 1 (meaning1320 q) (meaning1322 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1322 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1323 = true := by
  have hs : count1322 q = (countLit q [-76]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (1321)) (literal (valuationOf q) (1323)) (countLit q [-76]) (countLit q [-78, -79]) (count1322 q) 2 (meaning1321 q) (meaning1323 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1323 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-76]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78, -79])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1322)) (countLit q [-76]) (countLit q [-78, -79]) (count1322 q) 1 (meaningNeg76 q) (meaning1322 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1322 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1320 = false ∨ valuationOf q 1323 = true := by
  have hs : count1322 q = (countLit q [-76]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1323)) (countLit q [-76]) (countLit q [-78, -79]) (count1322 q) 1 1 (meaningNeg76 q) (meaning1320 q) (meaning1323 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1320 = false ∨ valuation q 1323 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E154.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112154
