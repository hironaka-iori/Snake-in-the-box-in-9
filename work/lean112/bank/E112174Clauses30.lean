import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1373 = true := by
  have hs : count1372 q = (countLit q [-78]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79, -80])
  have hm := merge_right (literal (valuationOf q) (1371)) (literal (valuationOf q) (1373)) (countLit q [-78]) (countLit q [-79, -80]) (count1372 q) 2 (meaning1371 q) (meaning1373 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1373 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1372 = true := by
  have hs : count1372 q = (countLit q [-78]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79, -80])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1372)) (countLit q [-78]) (countLit q [-79, -80]) (count1372 q) 1 (meaningNeg78 q) (meaning1372 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1372 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1370 = false ∨ valuationOf q 1373 = true := by
  have hs : count1372 q = (countLit q [-78]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1373)) (countLit q [-78]) (countLit q [-79, -80]) (count1372 q) 1 1 (meaningNeg78 q) (meaning1370 q) (meaning1373 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1370 = false ∨ valuation q 1373 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1375 = true := by
  have hs : count1375 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1375)) (countLit q [-83]) (countLit q [-85]) (count1375 q) 1 (meaningNeg85 q) (meaning1375 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1375 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1375 = true := by
  have hs : count1375 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1375)) (countLit q [-83]) (countLit q [-85]) (count1375 q) 1 (meaningNeg83 q) (meaning1375 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1375 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1377 = true := by
  have hs : count1377 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1377)) (countLit q [-87]) (countLit q [-90]) (count1377 q) 1 (meaningNeg90 q) (meaning1377 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1377 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 90 = true ∨ valuationOf q 1378 = true := by
  have hs : count1377 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (1378)) (countLit q [-87]) (countLit q [-90]) (count1377 q) 1 1 (meaningNeg87 q) (meaningNeg90 q) (meaning1378 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 90 = true ∨ valuation q 1378 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-83, -85]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -85]) (l₂ := [-87, -90])
  have hm := merge_right (literal (valuationOf q) (1377)) (literal (valuationOf q) (1379)) (countLit q [-83, -85]) (countLit q [-87, -90]) (count1379 q) 1 (meaning1377 q) (meaning1379 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1379 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1380 = true := by
  have hs : count1379 q = (countLit q [-83, -85]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -85]) (l₂ := [-87, -90])
  have hm := merge_right (literal (valuationOf q) (1378)) (literal (valuationOf q) (1380)) (countLit q [-83, -85]) (countLit q [-87, -90]) (count1379 q) 2 (meaning1378 q) (meaning1380 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1380 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-83, -85]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -85]) (l₂ := [-87, -90])
  have hm := merge_left (literal (valuationOf q) (1375)) (literal (valuationOf q) (1379)) (countLit q [-83, -85]) (countLit q [-87, -90]) (count1379 q) 1 (meaning1375 q) (meaning1379 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1379 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1380 = true := by
  have hs : count1379 q = (countLit q [-83, -85]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -85]) (l₂ := [-87, -90])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1377)) (literal (valuationOf q) (1380)) (countLit q [-83, -85]) (countLit q [-87, -90]) (count1379 q) 1 1 (meaning1375 q) (meaning1377 q) (meaning1380 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1377 = false ∨ valuation q 1380 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-78, -79, -80]) + (countLit q [-83, -85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80]) (l₂ := [-83, -85, -87, -90])
  have hm := merge_right (literal (valuationOf q) (1379)) (literal (valuationOf q) (1383)) (countLit q [-78, -79, -80]) (countLit q [-83, -85, -87, -90]) (count1383 q) 1 (meaning1379 q) (meaning1383 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1383 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-78, -79, -80]) + (countLit q [-83, -85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80]) (l₂ := [-83, -85, -87, -90])
  have hm := merge_right (literal (valuationOf q) (1380)) (literal (valuationOf q) (1384)) (countLit q [-78, -79, -80]) (countLit q [-83, -85, -87, -90]) (count1383 q) 2 (meaning1380 q) (meaning1384 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1384 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-78, -79, -80]) + (countLit q [-83, -85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80]) (l₂ := [-83, -85, -87, -90])
  have hm := merge_left (literal (valuationOf q) (1372)) (literal (valuationOf q) (1383)) (countLit q [-78, -79, -80]) (countLit q [-83, -85, -87, -90]) (count1383 q) 1 (meaning1372 q) (meaning1383 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1383 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-78, -79, -80]) + (countLit q [-83, -85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80]) (l₂ := [-83, -85, -87, -90])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1384)) (countLit q [-78, -79, -80]) (countLit q [-83, -85, -87, -90]) (count1383 q) 1 1 (meaning1372 q) (meaning1379 q) (meaning1384 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1379 = false ∨ valuation q 1384 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1385 = true := by
  have hs : count1383 q = (countLit q [-78, -79, -80]) + (countLit q [-83, -85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80]) (l₂ := [-83, -85, -87, -90])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1385)) (countLit q [-78, -79, -80]) (countLit q [-83, -85, -87, -90]) (count1383 q) 1 2 (meaning1372 q) (meaning1380 q) (meaning1385 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1380 = false ∨ valuation q 1385 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-78, -79, -80]) + (countLit q [-83, -85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80]) (l₂ := [-83, -85, -87, -90])
  have hm := merge_left (literal (valuationOf q) (1373)) (literal (valuationOf q) (1384)) (countLit q [-78, -79, -80]) (countLit q [-83, -85, -87, -90]) (count1383 q) 2 (meaning1373 q) (meaning1384 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1384 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1385 = true := by
  have hs : count1383 q = (countLit q [-78, -79, -80]) + (countLit q [-83, -85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80]) (l₂ := [-83, -85, -87, -90])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1385)) (countLit q [-78, -79, -80]) (countLit q [-83, -85, -87, -90]) (count1383 q) 2 1 (meaning1373 q) (meaning1379 q) (meaning1385 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1379 = false ∨ valuation q 1385 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-92]) + (countLit q [-93, -95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -95])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1392)) (countLit q [-92]) (countLit q [-93, -95]) (count1392 q) 1 (meaningNeg92 q) (meaning1392 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1392 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1395)) (countLit q [-98]) (countLit q [-100]) (count1395 q) 1 (meaningNeg100 q) (meaning1395 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1395 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1395)) (countLit q [-98]) (countLit q [-100]) (count1395 q) 1 (meaningNeg98 q) (meaning1395 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1395 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-98, -100]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -100]) (l₂ := [-101, -103])
  have hm := merge_left (literal (valuationOf q) (1395)) (literal (valuationOf q) (1399)) (countLit q [-98, -100]) (countLit q [-101, -103]) (count1399 q) 1 (meaning1395 q) (meaning1399 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1399 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-92, -93, -95]) + (countLit q [-98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-98, -100, -101, -103])
  have hm := merge_right (literal (valuationOf q) (1399)) (literal (valuationOf q) (1403)) (countLit q [-92, -93, -95]) (countLit q [-98, -100, -101, -103]) (count1403 q) 1 (meaning1399 q) (meaning1403 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1403 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-92, -93, -95]) + (countLit q [-98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-98, -100, -101, -103])
  have hm := merge_left (literal (valuationOf q) (1392)) (literal (valuationOf q) (1403)) (countLit q [-92, -93, -95]) (countLit q [-98, -100, -101, -103]) (count1403 q) 1 (meaning1392 q) (meaning1403 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1403 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-78, -79, -80, -83, -85, -87, -90]) + (countLit q [-92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80, -83, -85, -87, -90]) (l₂ := [-92, -93, -95, -98, -100, -101, -103])
  have hm := merge_right (literal (valuationOf q) (1403)) (literal (valuationOf q) (1410)) (countLit q [-78, -79, -80, -83, -85, -87, -90]) (countLit q [-92, -93, -95, -98, -100, -101, -103]) (count1410 q) 1 (meaning1403 q) (meaning1410 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1410 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-78, -79, -80, -83, -85, -87, -90]) + (countLit q [-92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80, -83, -85, -87, -90]) (l₂ := [-92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1411)) (countLit q [-78, -79, -80, -83, -85, -87, -90]) (countLit q [-92, -93, -95, -98, -100, -101, -103]) (count1410 q) 1 1 (meaning1383 q) (meaning1403 q) (meaning1411 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1403 = false ∨ valuation q 1411 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-78, -79, -80, -83, -85, -87, -90]) + (countLit q [-92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80, -83, -85, -87, -90]) (l₂ := [-92, -93, -95, -98, -100, -101, -103])
  have hm := merge_left (literal (valuationOf q) (1384)) (literal (valuationOf q) (1411)) (countLit q [-78, -79, -80, -83, -85, -87, -90]) (countLit q [-92, -93, -95, -98, -100, -101, -103]) (count1410 q) 2 (meaning1384 q) (meaning1411 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1411 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-78, -79, -80, -83, -85, -87, -90]) + (countLit q [-92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80, -83, -85, -87, -90]) (l₂ := [-92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1412)) (countLit q [-78, -79, -80, -83, -85, -87, -90]) (countLit q [-92, -93, -95, -98, -100, -101, -103]) (count1410 q) 2 1 (meaning1384 q) (meaning1403 q) (meaning1412 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1403 = false ∨ valuation q 1412 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-78, -79, -80, -83, -85, -87, -90]) + (countLit q [-92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80, -83, -85, -87, -90]) (l₂ := [-92, -93, -95, -98, -100, -101, -103])
  have hm := merge_left (literal (valuationOf q) (1385)) (literal (valuationOf q) (1412)) (countLit q [-78, -79, -80, -83, -85, -87, -90]) (countLit q [-92, -93, -95, -98, -100, -101, -103]) (count1410 q) 3 (meaning1385 q) (meaning1412 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1412 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1413 = true := by
  have hs : count1410 q = (countLit q [-78, -79, -80, -83, -85, -87, -90]) + (countLit q [-92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-78, -79, -80, -83, -85, -87, -90]) (l₂ := [-92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1413)) (countLit q [-78, -79, -80, -83, -85, -87, -90]) (countLit q [-92, -93, -95, -98, -100, -101, -103]) (count1410 q) 3 1 (meaning1385 q) (meaning1403 q) (meaning1413 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1403 = false ∨ valuation q 1413 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1425 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1425)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 1 2 (meaning1357 q) (meaning1411 q) (meaning1425 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1411 = false ∨ valuation q 1425 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1426 = true := by
  have hs : count1423 q = (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) + (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (l₂ := [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1426)) (countLit q [-52, -54, -55, -57, -60, -62, -63, -65, -68, -70, -71, -72, -76]) (countLit q [-78, -79, -80, -83, -85, -87, -90, -92, -93, -95, -98, -100, -101, -103]) (count1423 q) 1 3 (meaning1357 q) (meaning1412 q) (meaning1426 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1412 = false ∨ valuation q 1426 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E174.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112174
