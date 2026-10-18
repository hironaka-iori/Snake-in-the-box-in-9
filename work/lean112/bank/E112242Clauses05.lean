import E112242Semantics
import B112E242Inputs
namespace Snake9.Regrowth.E112242
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause161 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1382 = true := by
  have hs : count1382 q = (countLit q [-92]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -94])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1382)) (countLit q [-92]) (countLit q [-93, -94]) (count1382 q) 1 (meaningNeg92 q) (meaning1382 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1382 = true := counterClause161 (baseVal q)

theorem counterClause162 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1385 = true := by
  have hs : count1385 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1385)) (countLit q [-98]) (countLit q [-100]) (count1385 q) 1 (meaningNeg100 q) (meaning1385 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1385 = true := counterClause162 (baseVal q)

theorem counterClause163 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1385 = true := by
  have hs : count1385 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1385)) (countLit q [-98]) (countLit q [-100]) (count1385 q) 1 (meaningNeg98 q) (meaning1385 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1385 = true := counterClause163 (baseVal q)

theorem counterClause164 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1386 = true := by
  have hs : count1385 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1386)) (countLit q [-98]) (countLit q [-100]) (count1385 q) 1 1 (meaningNeg98 q) (meaningNeg100 q) (meaning1386 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 100 = true ∨ valuation q 1386 = true := counterClause164 (baseVal q)

theorem counterClause165 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1387 = true := by
  have hs : count1387 q = (countLit q [-101]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-103])
  have hm := merge_right (literal (valuationOf q) (-103)) (literal (valuationOf q) (1387)) (countLit q [-101]) (countLit q [-103]) (count1387 q) 1 (meaningNeg103 q) (meaning1387 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1387 = true := counterClause165 (baseVal q)

theorem counterClause166 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1387 = true := by
  have hs : count1387 q = (countLit q [-101]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-103])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1387)) (countLit q [-101]) (countLit q [-103]) (count1387 q) 1 (meaningNeg101 q) (meaning1387 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1387 = true := counterClause166 (baseVal q)

theorem counterClause167 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 103 = true ∨ valuationOf q 1388 = true := by
  have hs : count1387 q = (countLit q [-101]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-103])
  have hm := merge_two (literal (valuationOf q) (-101)) (literal (valuationOf q) (-103)) (literal (valuationOf q) (1388)) (countLit q [-101]) (countLit q [-103]) (count1387 q) 1 1 (meaningNeg101 q) (meaningNeg103 q) (meaning1388 q) hs
  change (! (valuationOf q 101)) = false ∨ (! (valuationOf q 103)) = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 1388 = true := counterClause167 (baseVal q)

theorem counterClause168 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1389 = true := by
  have hs : count1389 q = (countLit q [-98, -100]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -100]) (l₂ := [-101, -103])
  have hm := merge_right (literal (valuationOf q) (1387)) (literal (valuationOf q) (1389)) (countLit q [-98, -100]) (countLit q [-101, -103]) (count1389 q) 1 (meaning1387 q) (meaning1389 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1389 = true := counterClause168 (baseVal q)

theorem counterClause169 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1390 = true := by
  have hs : count1389 q = (countLit q [-98, -100]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -100]) (l₂ := [-101, -103])
  have hm := merge_right (literal (valuationOf q) (1388)) (literal (valuationOf q) (1390)) (countLit q [-98, -100]) (countLit q [-101, -103]) (count1389 q) 2 (meaning1388 q) (meaning1390 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1390 = true := counterClause169 (baseVal q)

theorem counterClause170 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1389 = true := by
  have hs : count1389 q = (countLit q [-98, -100]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -100]) (l₂ := [-101, -103])
  have hm := merge_left (literal (valuationOf q) (1385)) (literal (valuationOf q) (1389)) (countLit q [-98, -100]) (countLit q [-101, -103]) (count1389 q) 1 (meaning1385 q) (meaning1389 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1389 = true := counterClause170 (baseVal q)

theorem counterClause171 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1390 = true := by
  have hs : count1389 q = (countLit q [-98, -100]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -100]) (l₂ := [-101, -103])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1387)) (literal (valuationOf q) (1390)) (countLit q [-98, -100]) (countLit q [-101, -103]) (count1389 q) 1 1 (meaning1385 q) (meaning1387 q) (meaning1390 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1387 = false ∨ valuation q 1390 = true := counterClause171 (baseVal q)

theorem counterClause172 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1391 = true := by
  have hs : count1389 q = (countLit q [-98, -100]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -100]) (l₂ := [-101, -103])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1391)) (countLit q [-98, -100]) (countLit q [-101, -103]) (count1389 q) 1 2 (meaning1385 q) (meaning1388 q) (meaning1391 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1388 = false ∨ valuation q 1391 = true := counterClause172 (baseVal q)

theorem counterClause173 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1391 = true := by
  have hs : count1389 q = (countLit q [-98, -100]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -100]) (l₂ := [-101, -103])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1387)) (literal (valuationOf q) (1391)) (countLit q [-98, -100]) (countLit q [-101, -103]) (count1389 q) 2 1 (meaning1386 q) (meaning1387 q) (meaning1391 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1387 = false ∨ valuation q 1391 = true := counterClause173 (baseVal q)

theorem counterClause174 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1393 = true := by
  have hs : count1393 q = (countLit q [-92, -93, -94]) + (countLit q [-98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-98, -100, -101, -103])
  have hm := merge_right (literal (valuationOf q) (1389)) (literal (valuationOf q) (1393)) (countLit q [-92, -93, -94]) (countLit q [-98, -100, -101, -103]) (count1393 q) 1 (meaning1389 q) (meaning1393 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1393 = true := counterClause174 (baseVal q)

theorem counterClause175 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1394 = true := by
  have hs : count1393 q = (countLit q [-92, -93, -94]) + (countLit q [-98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-98, -100, -101, -103])
  have hm := merge_right (literal (valuationOf q) (1390)) (literal (valuationOf q) (1394)) (countLit q [-92, -93, -94]) (countLit q [-98, -100, -101, -103]) (count1393 q) 2 (meaning1390 q) (meaning1394 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1394 = true := counterClause175 (baseVal q)

theorem counterClause176 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1395 = true := by
  have hs : count1393 q = (countLit q [-92, -93, -94]) + (countLit q [-98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-98, -100, -101, -103])
  have hm := merge_right (literal (valuationOf q) (1391)) (literal (valuationOf q) (1395)) (countLit q [-92, -93, -94]) (countLit q [-98, -100, -101, -103]) (count1393 q) 3 (meaning1391 q) (meaning1395 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1395 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1393 = true := by
  have hs : count1393 q = (countLit q [-92, -93, -94]) + (countLit q [-98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-98, -100, -101, -103])
  have hm := merge_left (literal (valuationOf q) (1382)) (literal (valuationOf q) (1393)) (countLit q [-92, -93, -94]) (countLit q [-98, -100, -101, -103]) (count1393 q) 1 (meaning1382 q) (meaning1393 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1393 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1390 = false ∨ valuationOf q 1395 = true := by
  have hs : count1393 q = (countLit q [-92, -93, -94]) + (countLit q [-98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1382)) (literal (valuationOf q) (1390)) (literal (valuationOf q) (1395)) (countLit q [-92, -93, -94]) (countLit q [-98, -100, -101, -103]) (count1393 q) 1 2 (meaning1382 q) (meaning1390 q) (meaning1395 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1390 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1390 = false ∨ valuation q 1395 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1402 = true := by
  have hs : count1400 q = (countLit q [-78, -82, -83, -85, -87, -88, -91]) + (countLit q [-92, -93, -94, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-78, -82, -83, -85, -87, -88, -91]) (l₂ := [-92, -93, -94, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1402)) (countLit q [-78, -82, -83, -85, -87, -88, -91]) (countLit q [-92, -93, -94, -98, -100, -101, -103]) (count1400 q) 2 1 (meaning1374 q) (meaning1393 q) (meaning1402 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1393 = false ∨ valuation q 1402 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1403 = true := by
  have hs : count1400 q = (countLit q [-78, -82, -83, -85, -87, -88, -91]) + (countLit q [-92, -93, -94, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-78, -82, -83, -85, -87, -88, -91]) (l₂ := [-92, -93, -94, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1403)) (countLit q [-78, -82, -83, -85, -87, -88, -91]) (countLit q [-92, -93, -94, -98, -100, -101, -103]) (count1400 q) 2 2 (meaning1374 q) (meaning1394 q) (meaning1403 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1394 = false ∨ valuation q 1403 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1395 = false ∨ valuationOf q 1404 = true := by
  have hs : count1400 q = (countLit q [-78, -82, -83, -85, -87, -88, -91]) + (countLit q [-92, -93, -94, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-78, -82, -83, -85, -87, -88, -91]) (l₂ := [-92, -93, -94, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1395)) (literal (valuationOf q) (1404)) (countLit q [-78, -82, -83, -85, -87, -88, -91]) (countLit q [-92, -93, -94, -98, -100, -101, -103]) (count1400 q) 2 3 (meaning1374 q) (meaning1395 q) (meaning1404 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1395 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1395 = false ∨ valuation q 1404 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1404 = true := by
  have hs : count1400 q = (countLit q [-78, -82, -83, -85, -87, -88, -91]) + (countLit q [-92, -93, -94, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-78, -82, -83, -85, -87, -88, -91]) (l₂ := [-92, -93, -94, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1404)) (countLit q [-78, -82, -83, -85, -87, -88, -91]) (countLit q [-92, -93, -94, -98, -100, -101, -103]) (count1400 q) 3 2 (meaning1375 q) (meaning1394 q) (meaning1404 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1394 = false ∨ valuation q 1404 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1420 = true := by
  have hs : count1414 q = (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]) + (countLit q [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]) (l₂ := [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1420)) (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]) (countLit q [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) (count1414 q) 4 3 (meaning1349 q) (meaning1402 q) (meaning1420 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1402 = false ∨ valuation q 1420 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1421 = true := by
  have hs : count1414 q = (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]) + (countLit q [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]) (l₂ := [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1421)) (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]) (countLit q [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) (count1414 q) 4 4 (meaning1349 q) (meaning1403 q) (meaning1421 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1403 = false ∨ valuation q 1421 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1422 = true := by
  have hs : count1414 q = (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]) + (countLit q [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]) (l₂ := [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1422)) (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]) (countLit q [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) (count1414 q) 4 5 (meaning1349 q) (meaning1404 q) (meaning1422 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1404 = false ∨ valuation q 1422 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1421 = true := by
  have hs : count1414 q = (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]) + (countLit q [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]) (l₂ := [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1350)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1421)) (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]) (countLit q [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) (count1414 q) 5 3 (meaning1350 q) (meaning1402 q) (meaning1421 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1402 = false ∨ valuation q 1421 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1443 = true := by
  have hs : count1429 q = (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27, -28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) + (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77, -78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27, -28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) (l₂ := [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77, -78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1296)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1443)) (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27, -28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77, -78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) (count1429 q) 6 9 (meaning1296 q) (meaning1422 q) (meaning1443 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1422 = false ∨ valuation q 1443 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 1297 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1443 = true := by
  have hs : count1429 q = (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27, -28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) + (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77, -78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27, -28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) (l₂ := [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77, -78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1297)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1443)) (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27, -28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77, -78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) (count1429 q) 7 8 (meaning1297 q) (meaning1421 q) (meaning1443 q) hs
  change valuationOf q 1297 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 1297 = false ∨ valuation q 1421 = false ∨ valuation q 1443 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 1298 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1443 = true := by
  have hs : count1429 q = (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27, -28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) + (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77, -78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27, -28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) (l₂ := [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77, -78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1298)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1443)) (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27, -28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) (countLit q [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77, -78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]) (count1429 q) 8 7 (meaning1298 q) (meaning1420 q) (meaning1443 q) hs
  change valuationOf q 1298 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 1298 = false ∨ valuation q 1420 = false ∨ valuation q 1443 = true := counterClause189 (baseVal q)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false := by
  rw [value1443]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1429 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value97, value98, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (432 : Vertex) (433 : Vertex) (440 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E242.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h⟩

end
end Snake9.Regrowth.E112242
