import E112098Semantics
import B112E098Inputs
namespace Snake9.Regrowth.E112098
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause193 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1343 = true := by
  have hs : count1342 q = (countLit q [-94, -95]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-98, -99])
  have hm := merge_left (literal (valuationOf q) (1339)) (literal (valuationOf q) (1343)) (countLit q [-94, -95]) (countLit q [-98, -99]) (count1342 q) 2 (meaning1339 q) (meaning1343 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1343 = true := counterClause193 (baseVal q)

theorem counterClause194 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1344 = true := by
  have hs : count1342 q = (countLit q [-94, -95]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-98, -99])
  have hm := merge_two (literal (valuationOf q) (1339)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1344)) (countLit q [-94, -95]) (countLit q [-98, -99]) (count1342 q) 2 1 (meaning1339 q) (meaning1340 q) (meaning1344 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1340 = false ∨ valuation q 1344 = true := counterClause194 (baseVal q)

theorem counterClause195 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-89, -90, -92]) + (countLit q [-94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -92]) (l₂ := [-94, -95, -98, -99])
  have hm := merge_right (literal (valuationOf q) (1342)) (literal (valuationOf q) (1346)) (countLit q [-89, -90, -92]) (countLit q [-94, -95, -98, -99]) (count1346 q) 1 (meaning1342 q) (meaning1346 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1346 = true := counterClause195 (baseVal q)

theorem counterClause196 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1347 = true := by
  have hs : count1346 q = (countLit q [-89, -90, -92]) + (countLit q [-94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -92]) (l₂ := [-94, -95, -98, -99])
  have hm := merge_right (literal (valuationOf q) (1343)) (literal (valuationOf q) (1347)) (countLit q [-89, -90, -92]) (countLit q [-94, -95, -98, -99]) (count1346 q) 2 (meaning1343 q) (meaning1347 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1347 = true := counterClause196 (baseVal q)

theorem counterClause197 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1348 = true := by
  have hs : count1346 q = (countLit q [-89, -90, -92]) + (countLit q [-94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -92]) (l₂ := [-94, -95, -98, -99])
  have hm := merge_right (literal (valuationOf q) (1344)) (literal (valuationOf q) (1348)) (countLit q [-89, -90, -92]) (countLit q [-94, -95, -98, -99]) (count1346 q) 3 (meaning1344 q) (meaning1348 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1348 = true := counterClause197 (baseVal q)

theorem counterClause198 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-89, -90, -92]) + (countLit q [-94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -92]) (l₂ := [-94, -95, -98, -99])
  have hm := merge_left (literal (valuationOf q) (1335)) (literal (valuationOf q) (1346)) (countLit q [-89, -90, -92]) (countLit q [-94, -95, -98, -99]) (count1346 q) 1 (meaning1335 q) (meaning1346 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1346 = true := counterClause198 (baseVal q)

theorem counterClause199 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1342 = false ∨ valuationOf q 1347 = true := by
  have hs : count1346 q = (countLit q [-89, -90, -92]) + (countLit q [-94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -92]) (l₂ := [-94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1342)) (literal (valuationOf q) (1347)) (countLit q [-89, -90, -92]) (countLit q [-94, -95, -98, -99]) (count1346 q) 1 1 (meaning1335 q) (meaning1342 q) (meaning1347 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1342 = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1342 = false ∨ valuation q 1347 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1343 = false ∨ valuationOf q 1348 = true := by
  have hs : count1346 q = (countLit q [-89, -90, -92]) + (countLit q [-94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -92]) (l₂ := [-94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1343)) (literal (valuationOf q) (1348)) (countLit q [-89, -90, -92]) (countLit q [-94, -95, -98, -99]) (count1346 q) 1 2 (meaning1335 q) (meaning1343 q) (meaning1348 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1343 = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1343 = false ∨ valuation q 1348 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1354 = true := by
  have hs : count1353 q = (countLit q [-76, -77, -79, -82, -84, -85]) + (countLit q [-89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -82, -84, -85]) (l₂ := [-89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1354)) (countLit q [-76, -77, -79, -82, -84, -85]) (countLit q [-89, -90, -92, -94, -95, -98, -99]) (count1353 q) 1 1 (meaning1327 q) (meaning1346 q) (meaning1354 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1346 = false ∨ valuation q 1354 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1355 = true := by
  have hs : count1353 q = (countLit q [-76, -77, -79, -82, -84, -85]) + (countLit q [-89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -82, -84, -85]) (l₂ := [-89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1347)) (literal (valuationOf q) (1355)) (countLit q [-76, -77, -79, -82, -84, -85]) (countLit q [-89, -90, -92, -94, -95, -98, -99]) (count1353 q) 1 2 (meaning1327 q) (meaning1347 q) (meaning1355 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1347 = false ∨ valuation q 1355 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1354 = true := by
  have hs : count1353 q = (countLit q [-76, -77, -79, -82, -84, -85]) + (countLit q [-89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -82, -84, -85]) (l₂ := [-89, -90, -92, -94, -95, -98, -99])
  have hm := merge_left (literal (valuationOf q) (1328)) (literal (valuationOf q) (1354)) (countLit q [-76, -77, -79, -82, -84, -85]) (countLit q [-89, -90, -92, -94, -95, -98, -99]) (count1353 q) 2 (meaning1328 q) (meaning1354 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1354 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1355 = true := by
  have hs : count1353 q = (countLit q [-76, -77, -79, -82, -84, -85]) + (countLit q [-89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -82, -84, -85]) (l₂ := [-89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1355)) (countLit q [-76, -77, -79, -82, -84, -85]) (countLit q [-89, -90, -92, -94, -95, -98, -99]) (count1353 q) 2 1 (meaning1328 q) (meaning1346 q) (meaning1355 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1346 = false ∨ valuation q 1355 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1356 = true := by
  have hs : count1353 q = (countLit q [-76, -77, -79, -82, -84, -85]) + (countLit q [-89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -82, -84, -85]) (l₂ := [-89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1347)) (literal (valuationOf q) (1356)) (countLit q [-76, -77, -79, -82, -84, -85]) (countLit q [-89, -90, -92, -94, -95, -98, -99]) (count1353 q) 2 2 (meaning1328 q) (meaning1347 q) (meaning1356 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1347 = false ∨ valuation q 1356 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1357 = true := by
  have hs : count1353 q = (countLit q [-76, -77, -79, -82, -84, -85]) + (countLit q [-89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -82, -84, -85]) (l₂ := [-89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1348)) (literal (valuationOf q) (1357)) (countLit q [-76, -77, -79, -82, -84, -85]) (countLit q [-89, -90, -92, -94, -95, -98, -99]) (count1353 q) 2 3 (meaning1328 q) (meaning1348 q) (meaning1357 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1348 = false ∨ valuation q 1357 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1355 = true := by
  have hs : count1353 q = (countLit q [-76, -77, -79, -82, -84, -85]) + (countLit q [-89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -82, -84, -85]) (l₂ := [-89, -90, -92, -94, -95, -98, -99])
  have hm := merge_left (literal (valuationOf q) (1329)) (literal (valuationOf q) (1355)) (countLit q [-76, -77, -79, -82, -84, -85]) (countLit q [-89, -90, -92, -94, -95, -98, -99]) (count1353 q) 3 (meaning1329 q) (meaning1355 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1355 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1356 = true := by
  have hs : count1353 q = (countLit q [-76, -77, -79, -82, -84, -85]) + (countLit q [-89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -82, -84, -85]) (l₂ := [-89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1356)) (countLit q [-76, -77, -79, -82, -84, -85]) (countLit q [-89, -90, -92, -94, -95, -98, -99]) (count1353 q) 3 1 (meaning1329 q) (meaning1346 q) (meaning1356 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1346 = false ∨ valuation q 1356 = true := counterClause208 (baseVal q)

theorem counterClause209 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1356 = true := by
  have hs : count1353 q = (countLit q [-76, -77, -79, -82, -84, -85]) + (countLit q [-89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79, -82, -84, -85]) (l₂ := [-89, -90, -92, -94, -95, -98, -99])
  have hm := merge_left (literal (valuationOf q) (1330)) (literal (valuationOf q) (1356)) (countLit q [-76, -77, -79, -82, -84, -85]) (countLit q [-89, -90, -92, -94, -95, -98, -99]) (count1353 q) 4 (meaning1330 q) (meaning1356 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1356 = true := counterClause209 (baseVal q)

theorem counterClause210 (q : Nat → Bool) : valuationOf q 1307 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1368 = true := by
  have hs : count1364 q = (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) + (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (l₂ := [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1307)) (literal (valuationOf q) (1355)) (literal (valuationOf q) (1368)) (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) (count1364 q) 2 3 (meaning1307 q) (meaning1355 q) (meaning1368 q) hs
  change valuationOf q 1307 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 1307 = false ∨ valuation q 1355 = false ∨ valuation q 1368 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 1307 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1369 = true := by
  have hs : count1364 q = (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) + (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (l₂ := [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1307)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1369)) (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) (count1364 q) 2 4 (meaning1307 q) (meaning1356 q) (meaning1369 q) hs
  change valuationOf q 1307 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 1307 = false ∨ valuation q 1356 = false ∨ valuation q 1369 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 1307 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1370 = true := by
  have hs : count1364 q = (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) + (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (l₂ := [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1307)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1370)) (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) (count1364 q) 2 5 (meaning1307 q) (meaning1357 q) (meaning1370 q) hs
  change valuationOf q 1307 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 1307 = false ∨ valuation q 1357 = false ∨ valuation q 1370 = true := counterClause212 (baseVal q)

theorem counterClause213 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1368 = true := by
  have hs : count1364 q = (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) + (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (l₂ := [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1308)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1368)) (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) (count1364 q) 3 2 (meaning1308 q) (meaning1354 q) (meaning1368 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1354 = false ∨ valuation q 1368 = true := counterClause213 (baseVal q)

theorem counterClause214 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1369 = true := by
  have hs : count1364 q = (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) + (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (l₂ := [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1308)) (literal (valuationOf q) (1355)) (literal (valuationOf q) (1369)) (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) (count1364 q) 3 3 (meaning1308 q) (meaning1355 q) (meaning1369 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1355 = false ∨ valuation q 1369 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1370 = true := by
  have hs : count1364 q = (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) + (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (l₂ := [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1308)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1370)) (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) (count1364 q) 3 4 (meaning1308 q) (meaning1356 q) (meaning1370 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1356 = false ∨ valuation q 1370 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1369 = true := by
  have hs : count1364 q = (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) + (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (l₂ := [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1309)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1369)) (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]) (countLit q [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) (count1364 q) 4 2 (meaning1309 q) (meaning1354 q) (meaning1369 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1354 = false ∨ valuation q 1369 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1385 = true := by
  have hs : count1375 q = (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22, -24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) + (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73, -76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22, -24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) (l₂ := [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73, -76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1385)) (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22, -24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73, -76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) (count1375 q) 4 7 (meaning1262 q) (meaning1370 q) (meaning1385 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1370 = false ∨ valuation q 1385 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1385 = true := by
  have hs : count1375 q = (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22, -24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) + (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73, -76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22, -24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) (l₂ := [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73, -76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1385)) (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22, -24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73, -76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) (count1375 q) 5 6 (meaning1263 q) (meaning1369 q) (meaning1385 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1369 = false ∨ valuation q 1385 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1385 = true := by
  have hs : count1375 q = (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22, -24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) + (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73, -76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22, -24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) (l₂ := [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73, -76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1264)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1385)) (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22, -24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) (countLit q [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73, -76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]) (count1375 q) 6 5 (meaning1264 q) (meaning1368 q) (meaning1385 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1368 = false ∨ valuation q 1385 = true := counterClause219 (baseVal q)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false := by
  rw [value1385]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1375 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 12 = false := by
  rw [value2, value3, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (68 : Vertex) (69 : Vertex) (84 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value33, value34, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (229 : Vertex) (244 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E098.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h⟩

end
end Snake9.Regrowth.E112098
