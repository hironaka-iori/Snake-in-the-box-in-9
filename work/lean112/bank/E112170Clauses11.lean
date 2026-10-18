import E112170Semantics
import B112E170Inputs
namespace Snake9.Regrowth.E112170
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 1184 = false ∨ valuationOf q 1223 = false ∨ valuationOf q 1236 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1184)) (literal (valuationOf q) (1223)) (literal (valuationOf q) (1236)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 4 2 (meaning1184 q) (meaning1223 q) (meaning1236 q) hs
  change valuationOf q 1184 = false ∨ valuationOf q 1223 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 1184 = false ∨ valuation q 1223 = false ∨ valuation q 1236 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 1184 = false ∨ valuationOf q 1224 = false ∨ valuationOf q 1237 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1184)) (literal (valuationOf q) (1224)) (literal (valuationOf q) (1237)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 4 3 (meaning1184 q) (meaning1224 q) (meaning1237 q) hs
  change valuationOf q 1184 = false ∨ valuationOf q 1224 = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 1184 = false ∨ valuation q 1224 = false ∨ valuation q 1237 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1240 = true := by
  have hs : count1240 q = (countLit q [-52]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1240)) (countLit q [-52]) (countLit q [-56]) (count1240 q) 1 (meaningNeg56 q) (meaning1240 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1240 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1240 = true := by
  have hs : count1240 q = (countLit q [-52]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1240)) (countLit q [-52]) (countLit q [-56]) (count1240 q) 1 (meaningNeg52 q) (meaning1240 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1240 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 1240 = false ∨ valuationOf q 1242 = true := by
  have hs : count1242 q = (countLit q [-50]) + (countLit q [-52, -56]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52, -56])
  have hm := merge_right (literal (valuationOf q) (1240)) (literal (valuationOf q) (1242)) (countLit q [-50]) (countLit q [-52, -56]) (count1242 q) 1 (meaning1240 q) (meaning1242 q) hs
  change valuationOf q 1240 = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 1240 = false ∨ valuation q 1242 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1242 = true := by
  have hs : count1242 q = (countLit q [-50]) + (countLit q [-52, -56]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52, -56])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1242)) (countLit q [-50]) (countLit q [-52, -56]) (count1242 q) 1 (meaningNeg50 q) (meaning1242 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1242 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1240 = false ∨ valuationOf q 1243 = true := by
  have hs : count1242 q = (countLit q [-50]) + (countLit q [-52, -56]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52, -56])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1243)) (countLit q [-50]) (countLit q [-52, -56]) (count1242 q) 1 1 (meaningNeg50 q) (meaning1240 q) (meaning1243 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1240 = false ∨ valuation q 1243 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1245 = true := by
  have hs : count1245 q = (countLit q [-59]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1245)) (countLit q [-59]) (countLit q [-61]) (count1245 q) 1 (meaningNeg59 q) (meaning1245 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1245 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1245 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 1245 = false ∨ valuationOf q 1247 = true := by
  have hs : count1247 q = (countLit q [-58]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -61])
  have hm := merge_right (literal (valuationOf q) (1245)) (literal (valuationOf q) (1247)) (countLit q [-58]) (countLit q [-59, -61]) (count1247 q) 1 (meaning1245 q) (meaning1247 q) hs
  change valuationOf q 1245 = false ∨ valuationOf q 1247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 1245 = false ∨ valuation q 1247 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1250 = true := by
  have hs : count1250 q = (countLit q [-50, -52, -56]) + (countLit q [-58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56]) (l₂ := [-58, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1247)) (literal (valuationOf q) (1250)) (countLit q [-50, -52, -56]) (countLit q [-58, -59, -61]) (count1250 q) 1 (meaning1247 q) (meaning1250 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1250 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 1242 = false ∨ valuationOf q 1250 = true := by
  have hs : count1250 q = (countLit q [-50, -52, -56]) + (countLit q [-58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56]) (l₂ := [-58, -59, -61])
  have hm := merge_left (literal (valuationOf q) (1242)) (literal (valuationOf q) (1250)) (countLit q [-50, -52, -56]) (countLit q [-58, -59, -61]) (count1250 q) 1 (meaning1242 q) (meaning1250 q) hs
  change valuationOf q 1242 = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 1242 = false ∨ valuation q 1250 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1251 = true := by
  have hs : count1250 q = (countLit q [-50, -52, -56]) + (countLit q [-58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56]) (l₂ := [-58, -59, -61])
  have hm := merge_left (literal (valuationOf q) (1243)) (literal (valuationOf q) (1251)) (countLit q [-50, -52, -56]) (countLit q [-58, -59, -61]) (count1250 q) 2 (meaning1243 q) (meaning1251 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1251 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1261 = true := by
  have hs : count1261 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1261)) (countLit q [-72]) (countLit q [-73]) (count1261 q) 1 (meaningNeg73 q) (meaning1261 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1261 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1261 = true := by
  have hs : count1261 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1261)) (countLit q [-72]) (countLit q [-73]) (count1261 q) 1 (meaningNeg72 q) (meaning1261 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1261 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1262 = true := by
  have hs : count1261 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1262)) (countLit q [-72]) (countLit q [-73]) (count1261 q) 1 1 (meaningNeg72 q) (meaningNeg73 q) (meaning1262 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 1262 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1263 = true := by
  have hs : count1263 q = (countLit q [-70]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72, -73])
  have hm := merge_right (literal (valuationOf q) (1261)) (literal (valuationOf q) (1263)) (countLit q [-70]) (countLit q [-72, -73]) (count1263 q) 1 (meaning1261 q) (meaning1263 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1263 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1264 = true := by
  have hs : count1263 q = (countLit q [-70]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72, -73])
  have hm := merge_right (literal (valuationOf q) (1262)) (literal (valuationOf q) (1264)) (countLit q [-70]) (countLit q [-72, -73]) (count1263 q) 2 (meaning1262 q) (meaning1264 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1264 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1263 = true := by
  have hs : count1263 q = (countLit q [-70]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72, -73])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1263)) (countLit q [-70]) (countLit q [-72, -73]) (count1263 q) 1 (meaningNeg70 q) (meaning1263 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1263 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1261 = false ∨ valuationOf q 1264 = true := by
  have hs : count1263 q = (countLit q [-70]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (1261)) (literal (valuationOf q) (1264)) (countLit q [-70]) (countLit q [-72, -73]) (count1263 q) 1 1 (meaningNeg70 q) (meaning1261 q) (meaning1264 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1261 = false ∨ valuation q 1264 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1266 = true := by
  have hs : count1266 q = (countLit q [-64, -65, -67]) + (countLit q [-70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-64, -65, -67]) (l₂ := [-70, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1263)) (literal (valuationOf q) (1266)) (countLit q [-64, -65, -67]) (countLit q [-70, -72, -73]) (count1266 q) 1 (meaning1263 q) (meaning1266 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1266 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1267 = true := by
  have hs : count1266 q = (countLit q [-64, -65, -67]) + (countLit q [-70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-64, -65, -67]) (l₂ := [-70, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1264)) (literal (valuationOf q) (1267)) (countLit q [-64, -65, -67]) (countLit q [-70, -72, -73]) (count1266 q) 2 (meaning1264 q) (meaning1267 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1267 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 1266 = false ∨ valuationOf q 1272 = true := by
  have hs : count1272 q = (countLit q [-50, -52, -56, -58, -59, -61]) + (countLit q [-64, -65, -67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61]) (l₂ := [-64, -65, -67, -70, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1266)) (literal (valuationOf q) (1272)) (countLit q [-50, -52, -56, -58, -59, -61]) (countLit q [-64, -65, -67, -70, -72, -73]) (count1272 q) 1 (meaning1266 q) (meaning1272 q) hs
  change valuationOf q 1266 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 1266 = false ∨ valuation q 1272 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 1267 = false ∨ valuationOf q 1273 = true := by
  have hs : count1272 q = (countLit q [-50, -52, -56, -58, -59, -61]) + (countLit q [-64, -65, -67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61]) (l₂ := [-64, -65, -67, -70, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1267)) (literal (valuationOf q) (1273)) (countLit q [-50, -52, -56, -58, -59, -61]) (countLit q [-64, -65, -67, -70, -72, -73]) (count1272 q) 2 (meaning1267 q) (meaning1273 q) hs
  change valuationOf q 1267 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 1267 = false ∨ valuation q 1273 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 1250 = false ∨ valuationOf q 1272 = true := by
  have hs : count1272 q = (countLit q [-50, -52, -56, -58, -59, -61]) + (countLit q [-64, -65, -67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61]) (l₂ := [-64, -65, -67, -70, -72, -73])
  have hm := merge_left (literal (valuationOf q) (1250)) (literal (valuationOf q) (1272)) (countLit q [-50, -52, -56, -58, -59, -61]) (countLit q [-64, -65, -67, -70, -72, -73]) (count1272 q) 1 (meaning1250 q) (meaning1272 q) hs
  change valuationOf q 1250 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 1250 = false ∨ valuation q 1272 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 1250 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1273 = true := by
  have hs : count1272 q = (countLit q [-50, -52, -56, -58, -59, -61]) + (countLit q [-64, -65, -67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61]) (l₂ := [-64, -65, -67, -70, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1250)) (literal (valuationOf q) (1266)) (literal (valuationOf q) (1273)) (countLit q [-50, -52, -56, -58, -59, -61]) (countLit q [-64, -65, -67, -70, -72, -73]) (count1272 q) 1 1 (meaning1250 q) (meaning1266 q) (meaning1273 q) hs
  change valuationOf q 1250 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 1250 = false ∨ valuation q 1266 = false ∨ valuation q 1273 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 1250 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1274 = true := by
  have hs : count1272 q = (countLit q [-50, -52, -56, -58, -59, -61]) + (countLit q [-64, -65, -67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61]) (l₂ := [-64, -65, -67, -70, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1250)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1274)) (countLit q [-50, -52, -56, -58, -59, -61]) (countLit q [-64, -65, -67, -70, -72, -73]) (count1272 q) 1 2 (meaning1250 q) (meaning1267 q) (meaning1274 q) hs
  change valuationOf q 1250 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 1250 = false ∨ valuation q 1267 = false ∨ valuation q 1274 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1273 = true := by
  have hs : count1272 q = (countLit q [-50, -52, -56, -58, -59, -61]) + (countLit q [-64, -65, -67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61]) (l₂ := [-64, -65, -67, -70, -72, -73])
  have hm := merge_left (literal (valuationOf q) (1251)) (literal (valuationOf q) (1273)) (countLit q [-50, -52, -56, -58, -59, -61]) (countLit q [-64, -65, -67, -70, -72, -73]) (count1272 q) 2 (meaning1251 q) (meaning1273 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1273 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1274 = true := by
  have hs : count1272 q = (countLit q [-50, -52, -56, -58, -59, -61]) + (countLit q [-64, -65, -67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61]) (l₂ := [-64, -65, -67, -70, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1266)) (literal (valuationOf q) (1274)) (countLit q [-50, -52, -56, -58, -59, -61]) (countLit q [-64, -65, -67, -70, -72, -73]) (count1272 q) 2 1 (meaning1251 q) (meaning1266 q) (meaning1274 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1266 = false ∨ valuation q 1274 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1281 = true := by
  have hs : count1281 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1281)) (countLit q [-77]) (countLit q [-79]) (count1281 q) 1 (meaningNeg79 q) (meaning1281 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1281 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1281 = true := by
  have hs : count1281 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1281)) (countLit q [-77]) (countLit q [-79]) (count1281 q) 1 (meaningNeg77 q) (meaning1281 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1281 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1282 = true := by
  have hs : count1281 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1282)) (countLit q [-77]) (countLit q [-79]) (count1281 q) 1 1 (meaningNeg77 q) (meaningNeg79 q) (meaning1282 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 1282 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 1281 = false ∨ valuationOf q 1283 = true := by
  have hs : count1283 q = (countLit q [-75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77, -79])
  have hm := merge_right (literal (valuationOf q) (1281)) (literal (valuationOf q) (1283)) (countLit q [-75]) (countLit q [-77, -79]) (count1283 q) 1 (meaning1281 q) (meaning1283 q) hs
  change valuationOf q 1281 = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 1281 = false ∨ valuation q 1283 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E170.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112170
