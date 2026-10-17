import E112182Semantics
import B112E182Inputs
namespace Snake9.Regrowth.E112182
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause193 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1330)) (countLit q [-75]) (countLit q [-77]) (count1330 q) 1 (meaningNeg75 q) (meaning1330 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1330 = true := counterClause193 (baseVal q)

theorem counterClause194 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1330 = false ∨ valuationOf q 1333 = true := by
  have hs : count1332 q = (countLit q [-74]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -77])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1333)) (countLit q [-74]) (countLit q [-75, -77]) (count1332 q) 1 1 (meaningNeg74 q) (meaning1330 q) (meaning1333 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1330 = false ∨ valuation q 1333 = true := counterClause194 (baseVal q)

theorem counterClause195 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1336 = true := by
  have hs : count1335 q = (countLit q [-68, -69, -73]) + (countLit q [-74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-68, -69, -73]) (l₂ := [-74, -75, -77])
  have hm := merge_right (literal (valuationOf q) (1333)) (literal (valuationOf q) (1336)) (countLit q [-68, -69, -73]) (countLit q [-74, -75, -77]) (count1335 q) 2 (meaning1333 q) (meaning1336 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1336 = true := counterClause195 (baseVal q)

theorem counterClause196 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-54, -58, -60, -63, -64, -66]) + (countLit q [-68, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66]) (l₂ := [-68, -69, -73, -74, -75, -77])
  have hm := merge_left (literal (valuationOf q) (1319)) (literal (valuationOf q) (1341)) (countLit q [-54, -58, -60, -63, -64, -66]) (countLit q [-68, -69, -73, -74, -75, -77]) (count1341 q) 1 (meaning1319 q) (meaning1341 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1341 = true := counterClause196 (baseVal q)

theorem counterClause197 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1342 = true := by
  have hs : count1341 q = (countLit q [-54, -58, -60, -63, -64, -66]) + (countLit q [-68, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66]) (l₂ := [-68, -69, -73, -74, -75, -77])
  have hm := merge_left (literal (valuationOf q) (1320)) (literal (valuationOf q) (1342)) (countLit q [-54, -58, -60, -63, -64, -66]) (countLit q [-68, -69, -73, -74, -75, -77]) (count1341 q) 2 (meaning1320 q) (meaning1342 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1342 = true := counterClause197 (baseVal q)

theorem counterClause198 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1336 = false ∨ valuationOf q 1344 = true := by
  have hs : count1341 q = (countLit q [-54, -58, -60, -63, -64, -66]) + (countLit q [-68, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66]) (l₂ := [-68, -69, -73, -74, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1320)) (literal (valuationOf q) (1336)) (literal (valuationOf q) (1344)) (countLit q [-54, -58, -60, -63, -64, -66]) (countLit q [-68, -69, -73, -74, -75, -77]) (count1341 q) 2 2 (meaning1320 q) (meaning1336 q) (meaning1344 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1336 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1336 = false ∨ valuation q 1344 = true := counterClause198 (baseVal q)

theorem counterClause199 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1343 = true := by
  have hs : count1341 q = (countLit q [-54, -58, -60, -63, -64, -66]) + (countLit q [-68, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66]) (l₂ := [-68, -69, -73, -74, -75, -77])
  have hm := merge_left (literal (valuationOf q) (1321)) (literal (valuationOf q) (1343)) (countLit q [-54, -58, -60, -63, -64, -66]) (countLit q [-68, -69, -73, -74, -75, -77]) (count1341 q) 3 (meaning1321 q) (meaning1343 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1343 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1344 = true := by
  have hs : count1341 q = (countLit q [-54, -58, -60, -63, -64, -66]) + (countLit q [-68, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66]) (l₂ := [-68, -69, -73, -74, -75, -77])
  have hm := merge_left (literal (valuationOf q) (1322)) (literal (valuationOf q) (1344)) (countLit q [-54, -58, -60, -63, -64, -66]) (countLit q [-68, -69, -73, -74, -75, -77]) (count1341 q) 4 (meaning1322 q) (meaning1344 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1344 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (1349)) (countLit q [-82]) (countLit q [-83]) (count1349 q) 1 (meaningNeg83 q) (meaning1349 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1349 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1349)) (countLit q [-82]) (countLit q [-83]) (count1349 q) 1 (meaningNeg82 q) (meaning1349 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1349 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-81]) + (countLit q [-82, -83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -83])
  have hm := merge_right (literal (valuationOf q) (1349)) (literal (valuationOf q) (1351)) (countLit q [-81]) (countLit q [-82, -83]) (count1351 q) 1 (meaning1349 q) (meaning1351 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1351 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-81]) + (countLit q [-82, -83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -83])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1351)) (countLit q [-81]) (countLit q [-82, -83]) (count1351 q) 1 (meaningNeg81 q) (meaning1351 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1351 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1354)) (countLit q [-88]) (countLit q [-90]) (count1354 q) 1 (meaningNeg90 q) (meaning1354 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1354 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1354)) (countLit q [-88]) (countLit q [-90]) (count1354 q) 1 (meaningNeg88 q) (meaning1354 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1354 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-84]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-88, -90])
  have hm := merge_right (literal (valuationOf q) (1354)) (literal (valuationOf q) (1356)) (countLit q [-84]) (countLit q [-88, -90]) (count1356 q) 1 (meaning1354 q) (meaning1356 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1356 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1359 = true := by
  have hs : count1359 q = (countLit q [-81, -82, -83]) + (countLit q [-84, -88, -90]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-84, -88, -90])
  have hm := merge_left (literal (valuationOf q) (1351)) (literal (valuationOf q) (1359)) (countLit q [-81, -82, -83]) (countLit q [-84, -88, -90]) (count1359 q) 1 (meaning1351 q) (meaning1359 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1359 = true := counterClause208 (baseVal q)

theorem counterClause209 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1360 = true := by
  have hs : count1359 q = (countLit q [-81, -82, -83]) + (countLit q [-84, -88, -90]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-84, -88, -90])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1360)) (countLit q [-81, -82, -83]) (countLit q [-84, -88, -90]) (count1359 q) 1 1 (meaning1351 q) (meaning1356 q) (meaning1360 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1356 = false ∨ valuation q 1360 = true := counterClause209 (baseVal q)

theorem counterClause210 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-93]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1365)) (countLit q [-93]) (countLit q [-97]) (count1365 q) 1 (meaningNeg93 q) (meaning1365 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1365 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1367 = true := by
  have hs : count1367 q = (countLit q [-91]) + (countLit q [-93, -97]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93, -97])
  have hm := merge_right (literal (valuationOf q) (1365)) (literal (valuationOf q) (1367)) (countLit q [-91]) (countLit q [-93, -97]) (count1367 q) 1 (meaning1365 q) (meaning1367 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1367 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1367 = true := by
  have hs : count1367 q = (countLit q [-91]) + (countLit q [-93, -97]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93, -97])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1367)) (countLit q [-91]) (countLit q [-93, -97]) (count1367 q) 1 (meaningNeg91 q) (meaning1367 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1367 = true := counterClause212 (baseVal q)

theorem counterClause213 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1370)) (countLit q [-99]) (countLit q [-100]) (count1370 q) 1 (meaningNeg100 q) (meaning1370 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1370 = true := counterClause213 (baseVal q)

theorem counterClause214 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1370)) (countLit q [-99]) (countLit q [-100]) (count1370 q) 1 (meaningNeg99 q) (meaning1370 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1370 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1372 = true := by
  have hs : count1372 q = (countLit q [-98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -100])
  have hm := merge_right (literal (valuationOf q) (1370)) (literal (valuationOf q) (1372)) (countLit q [-98]) (countLit q [-99, -100]) (count1372 q) 1 (meaning1370 q) (meaning1372 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1372 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1372 = true := by
  have hs : count1372 q = (countLit q [-98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -100])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1372)) (countLit q [-98]) (countLit q [-99, -100]) (count1372 q) 1 (meaningNeg98 q) (meaning1372 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1372 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1375 = true := by
  have hs : count1375 q = (countLit q [-91, -93, -97]) + (countLit q [-98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -97]) (l₂ := [-98, -99, -100])
  have hm := merge_right (literal (valuationOf q) (1372)) (literal (valuationOf q) (1375)) (countLit q [-91, -93, -97]) (countLit q [-98, -99, -100]) (count1375 q) 1 (meaning1372 q) (meaning1375 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1375 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1376 = true := by
  have hs : count1375 q = (countLit q [-91, -93, -97]) + (countLit q [-98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -97]) (l₂ := [-98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1372)) (literal (valuationOf q) (1376)) (countLit q [-91, -93, -97]) (countLit q [-98, -99, -100]) (count1375 q) 1 1 (meaning1367 q) (meaning1372 q) (meaning1376 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1372 = false ∨ valuation q 1376 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-81, -82, -83, -84, -88, -90]) + (countLit q [-91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83, -84, -88, -90]) (l₂ := [-91, -93, -97, -98, -99, -100])
  have hm := merge_left (literal (valuationOf q) (1359)) (literal (valuationOf q) (1381)) (countLit q [-81, -82, -83, -84, -88, -90]) (countLit q [-91, -93, -97, -98, -99, -100]) (count1381 q) 1 (meaning1359 q) (meaning1381 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1381 = true := counterClause219 (baseVal q)

theorem counterClause220 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-81, -82, -83, -84, -88, -90]) + (countLit q [-91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83, -84, -88, -90]) (l₂ := [-91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1382)) (countLit q [-81, -82, -83, -84, -88, -90]) (countLit q [-91, -93, -97, -98, -99, -100]) (count1381 q) 1 1 (meaning1359 q) (meaning1375 q) (meaning1382 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1375 = false ∨ valuation q 1382 = true := counterClause220 (baseVal q)

theorem counterClause221 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1383 = true := by
  have hs : count1381 q = (countLit q [-81, -82, -83, -84, -88, -90]) + (countLit q [-91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83, -84, -88, -90]) (l₂ := [-91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1383)) (countLit q [-81, -82, -83, -84, -88, -90]) (countLit q [-91, -93, -97, -98, -99, -100]) (count1381 q) 1 2 (meaning1359 q) (meaning1376 q) (meaning1383 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1376 = false ∨ valuation q 1383 = true := counterClause221 (baseVal q)

theorem counterClause222 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1383 = true := by
  have hs : count1381 q = (countLit q [-81, -82, -83, -84, -88, -90]) + (countLit q [-91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83, -84, -88, -90]) (l₂ := [-91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1360)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1383)) (countLit q [-81, -82, -83, -84, -88, -90]) (countLit q [-91, -93, -97, -98, -99, -100]) (count1381 q) 2 1 (meaning1360 q) (meaning1375 q) (meaning1383 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1375 = false ∨ valuation q 1383 = true := counterClause222 (baseVal q)

theorem counterClause223 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1384 = true := by
  have hs : count1381 q = (countLit q [-81, -82, -83, -84, -88, -90]) + (countLit q [-91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83, -84, -88, -90]) (l₂ := [-91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1360)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1384)) (countLit q [-81, -82, -83, -84, -88, -90]) (countLit q [-91, -93, -97, -98, -99, -100]) (count1381 q) 2 2 (meaning1360 q) (meaning1376 q) (meaning1384 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1376 = false ∨ valuation q 1384 = true := counterClause223 (baseVal q)

theorem counterClause224 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1391 = true := by
  have hs : count1389 q = (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1391)) (countLit q [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]) (count1389 q) 1 2 (meaning1341 q) (meaning1382 q) (meaning1391 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1382 = false ∨ valuation q 1391 = true := counterClause224 (baseVal q)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E182.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112182
