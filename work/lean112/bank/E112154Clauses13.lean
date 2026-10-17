import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-76, -78, -79, -80, -83, -87]) + (countLit q [-88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -80, -83, -87]) (l₂ := [-88, -91, -93, -94, -95, -98, -101])
  have hm := merge_left (literal (valuationOf q) (1330)) (literal (valuationOf q) (1356)) (countLit q [-76, -78, -79, -80, -83, -87]) (countLit q [-88, -91, -93, -94, -95, -98, -101]) (count1356 q) 1 (meaning1330 q) (meaning1356 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1356 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1357 = true := by
  have hs : count1356 q = (countLit q [-76, -78, -79, -80, -83, -87]) + (countLit q [-88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -80, -83, -87]) (l₂ := [-88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1357)) (countLit q [-76, -78, -79, -80, -83, -87]) (countLit q [-88, -91, -93, -94, -95, -98, -101]) (count1356 q) 1 1 (meaning1330 q) (meaning1349 q) (meaning1357 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1349 = false ∨ valuation q 1357 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1358 = true := by
  have hs : count1356 q = (countLit q [-76, -78, -79, -80, -83, -87]) + (countLit q [-88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -80, -83, -87]) (l₂ := [-88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1358)) (countLit q [-76, -78, -79, -80, -83, -87]) (countLit q [-88, -91, -93, -94, -95, -98, -101]) (count1356 q) 1 2 (meaning1330 q) (meaning1350 q) (meaning1358 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1350 = false ∨ valuation q 1358 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1359 = true := by
  have hs : count1356 q = (countLit q [-76, -78, -79, -80, -83, -87]) + (countLit q [-88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -80, -83, -87]) (l₂ := [-88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1359)) (countLit q [-76, -78, -79, -80, -83, -87]) (countLit q [-88, -91, -93, -94, -95, -98, -101]) (count1356 q) 1 3 (meaning1330 q) (meaning1351 q) (meaning1359 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1351 = false ∨ valuation q 1359 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1358 = true := by
  have hs : count1356 q = (countLit q [-76, -78, -79, -80, -83, -87]) + (countLit q [-88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -80, -83, -87]) (l₂ := [-88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1358)) (countLit q [-76, -78, -79, -80, -83, -87]) (countLit q [-88, -91, -93, -94, -95, -98, -101]) (count1356 q) 2 1 (meaning1331 q) (meaning1349 q) (meaning1358 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1349 = false ∨ valuation q 1358 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1359 = true := by
  have hs : count1356 q = (countLit q [-76, -78, -79, -80, -83, -87]) + (countLit q [-88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -80, -83, -87]) (l₂ := [-88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1359)) (countLit q [-76, -78, -79, -80, -83, -87]) (countLit q [-88, -91, -93, -94, -95, -98, -101]) (count1356 q) 2 2 (meaning1331 q) (meaning1350 q) (meaning1359 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1350 = false ∨ valuation q 1359 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1360 = true := by
  have hs : count1356 q = (countLit q [-76, -78, -79, -80, -83, -87]) + (countLit q [-88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -80, -83, -87]) (l₂ := [-88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1360)) (countLit q [-76, -78, -79, -80, -83, -87]) (countLit q [-88, -91, -93, -94, -95, -98, -101]) (count1356 q) 2 3 (meaning1331 q) (meaning1351 q) (meaning1360 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1351 = false ∨ valuation q 1360 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1359 = true := by
  have hs : count1356 q = (countLit q [-76, -78, -79, -80, -83, -87]) + (countLit q [-88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -80, -83, -87]) (l₂ := [-88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1359)) (countLit q [-76, -78, -79, -80, -83, -87]) (countLit q [-88, -91, -93, -94, -95, -98, -101]) (count1356 q) 3 1 (meaning1332 q) (meaning1349 q) (meaning1359 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1349 = false ∨ valuation q 1359 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1369 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1310)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1369)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 1 3 (meaning1310 q) (meaning1358 q) (meaning1369 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1358 = false ∨ valuation q 1369 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1370 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1310)) (literal (valuationOf q) (1359)) (literal (valuationOf q) (1370)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 1 4 (meaning1310 q) (meaning1359 q) (meaning1370 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1359 = false ∨ valuation q 1370 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1371 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1310)) (literal (valuationOf q) (1360)) (literal (valuationOf q) (1371)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 1 5 (meaning1310 q) (meaning1360 q) (meaning1371 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1360 = false ∨ valuation q 1371 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1367 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_left (literal (valuationOf q) (1311)) (literal (valuationOf q) (1367)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 2 (meaning1311 q) (meaning1367 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1367 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1368 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1368)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 2 1 (meaning1311 q) (meaning1356 q) (meaning1368 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1356 = false ∨ valuation q 1368 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1369 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1369)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 2 2 (meaning1311 q) (meaning1357 q) (meaning1369 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1357 = false ∨ valuation q 1369 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1370 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1370)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 2 3 (meaning1311 q) (meaning1358 q) (meaning1370 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1358 = false ∨ valuation q 1370 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1371 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1359)) (literal (valuationOf q) (1371)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 2 4 (meaning1311 q) (meaning1359 q) (meaning1371 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1359 = false ∨ valuation q 1371 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1368 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_left (literal (valuationOf q) (1312)) (literal (valuationOf q) (1368)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 3 (meaning1312 q) (meaning1368 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1368 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1369 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1369)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 3 1 (meaning1312 q) (meaning1356 q) (meaning1369 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1356 = false ∨ valuation q 1369 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1370 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1370)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 3 2 (meaning1312 q) (meaning1357 q) (meaning1370 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1357 = false ∨ valuation q 1370 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1371 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1371)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 3 3 (meaning1312 q) (meaning1358 q) (meaning1371 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1358 = false ∨ valuation q 1371 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1370 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1313)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1370)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 4 1 (meaning1313 q) (meaning1356 q) (meaning1370 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1356 = false ∨ valuation q 1370 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1371 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1313)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1371)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 4 2 (meaning1313 q) (meaning1357 q) (meaning1371 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1357 = false ∨ valuation q 1371 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 1314 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1371 = true := by
  have hs : count1366 q = (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) + (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (l₂ := [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1314)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1371)) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73]) (countLit q [-76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1366 q) 5 1 (meaning1314 q) (meaning1356 q) (meaning1371 q) hs
  change valuationOf q 1314 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 1314 = false ∨ valuation q 1356 = false ∨ valuation q 1371 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1385 = true := by
  have hs : count1376 q = (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) + (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (l₂ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1371)) (literal (valuationOf q) (1385)) (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1376 q) 4 6 (meaning1271 q) (meaning1371 q) (meaning1385 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1371 = false ∨ valuation q 1385 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1385 = true := by
  have hs : count1376 q = (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) + (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (l₂ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1385)) (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1376 q) 5 5 (meaning1272 q) (meaning1370 q) (meaning1385 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1370 = false ∨ valuation q 1385 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1385 = true := by
  have hs : count1376 q = (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) + (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (l₂ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1385)) (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1376 q) 6 4 (meaning1273 q) (meaning1369 q) (meaning1385 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1369 = false ∨ valuation q 1385 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1385 = true := by
  have hs : count1376 q = (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) + (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (l₂ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1385)) (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1376 q) 7 3 (meaning1274 q) (meaning1368 q) (meaning1385 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1368 = false ∨ valuation q 1385 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1385 = true := by
  have hs : count1376 q = (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) + (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (l₂ := [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1275)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1385)) (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26, -28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (countLit q [-53, -54, -56, -59, -60, -62, -65, -67, -68, -69, -72, -73, -76, -78, -79, -80, -83, -87, -88, -91, -93, -94, -95, -98, -101]) (count1376 q) 8 2 (meaning1275 q) (meaning1367 q) (meaning1385 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1367 = false ∨ valuation q 1385 = true := counterClause444 (baseVal q)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false := by
  rw [value1385]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1376 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value35, value36, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value73, value74, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (422 : Vertex) (423 : Vertex) (430 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value75, value76, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (425 : Vertex) (440 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E154.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112154
