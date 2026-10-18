import E112170Semantics
import B112E170Inputs
namespace Snake9.Regrowth.E112170
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 1306 = false ∨ valuationOf q 1310 = true := by
  have hs : count1310 q = (countLit q [-87, -88, -90]) + (countLit q [-93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-87, -88, -90]) (l₂ := [-93, -95, -96, -98])
  have hm := merge_right (literal (valuationOf q) (1306)) (literal (valuationOf q) (1310)) (countLit q [-87, -88, -90]) (countLit q [-93, -95, -96, -98]) (count1310 q) 1 (meaning1306 q) (meaning1310 q) hs
  change valuationOf q 1306 = false ∨ valuationOf q 1310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 1306 = false ∨ valuation q 1310 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 1307 = false ∨ valuationOf q 1311 = true := by
  have hs : count1310 q = (countLit q [-87, -88, -90]) + (countLit q [-93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-87, -88, -90]) (l₂ := [-93, -95, -96, -98])
  have hm := merge_right (literal (valuationOf q) (1307)) (literal (valuationOf q) (1311)) (countLit q [-87, -88, -90]) (countLit q [-93, -95, -96, -98]) (count1310 q) 2 (meaning1307 q) (meaning1311 q) hs
  change valuationOf q 1307 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 1307 = false ∨ valuation q 1311 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 1299 = false ∨ valuationOf q 1310 = true := by
  have hs : count1310 q = (countLit q [-87, -88, -90]) + (countLit q [-93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-87, -88, -90]) (l₂ := [-93, -95, -96, -98])
  have hm := merge_left (literal (valuationOf q) (1299)) (literal (valuationOf q) (1310)) (countLit q [-87, -88, -90]) (countLit q [-93, -95, -96, -98]) (count1310 q) 1 (meaning1299 q) (meaning1310 q) hs
  change valuationOf q 1299 = false ∨ valuationOf q 1310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 1299 = false ∨ valuation q 1310 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 1299 = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1311 = true := by
  have hs : count1310 q = (countLit q [-87, -88, -90]) + (countLit q [-93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-87, -88, -90]) (l₂ := [-93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1299)) (literal (valuationOf q) (1306)) (literal (valuationOf q) (1311)) (countLit q [-87, -88, -90]) (countLit q [-93, -95, -96, -98]) (count1310 q) 1 1 (meaning1299 q) (meaning1306 q) (meaning1311 q) hs
  change valuationOf q 1299 = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 1299 = false ∨ valuation q 1306 = false ∨ valuation q 1311 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 1300 = false ∨ valuationOf q 1311 = true := by
  have hs : count1310 q = (countLit q [-87, -88, -90]) + (countLit q [-93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-87, -88, -90]) (l₂ := [-93, -95, -96, -98])
  have hm := merge_left (literal (valuationOf q) (1300)) (literal (valuationOf q) (1311)) (countLit q [-87, -88, -90]) (countLit q [-93, -95, -96, -98]) (count1310 q) 2 (meaning1300 q) (meaning1311 q) hs
  change valuationOf q 1300 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 1300 = false ∨ valuation q 1311 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 1300 = false ∨ valuationOf q 1307 = false ∨ valuationOf q 1313 = true := by
  have hs : count1310 q = (countLit q [-87, -88, -90]) + (countLit q [-93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-87, -88, -90]) (l₂ := [-93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1300)) (literal (valuationOf q) (1307)) (literal (valuationOf q) (1313)) (countLit q [-87, -88, -90]) (countLit q [-93, -95, -96, -98]) (count1310 q) 2 2 (meaning1300 q) (meaning1307 q) (meaning1313 q) hs
  change valuationOf q 1300 = false ∨ valuationOf q 1307 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 1300 = false ∨ valuation q 1307 = false ∨ valuation q 1313 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-75, -77, -79, -80, -82, -85]) + (countLit q [-87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79, -80, -82, -85]) (l₂ := [-87, -88, -90, -93, -95, -96, -98])
  have hm := merge_right (literal (valuationOf q) (1310)) (literal (valuationOf q) (1317)) (countLit q [-75, -77, -79, -80, -82, -85]) (countLit q [-87, -88, -90, -93, -95, -96, -98]) (count1317 q) 1 (meaning1310 q) (meaning1317 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1317 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1310 = false ∨ valuationOf q 1318 = true := by
  have hs : count1317 q = (countLit q [-75, -77, -79, -80, -82, -85]) + (countLit q [-87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79, -80, -82, -85]) (l₂ := [-87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1310)) (literal (valuationOf q) (1318)) (countLit q [-75, -77, -79, -80, -82, -85]) (countLit q [-87, -88, -90, -93, -95, -96, -98]) (count1317 q) 1 1 (meaning1291 q) (meaning1310 q) (meaning1318 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1310 = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1310 = false ∨ valuation q 1318 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1311 = false ∨ valuationOf q 1319 = true := by
  have hs : count1317 q = (countLit q [-75, -77, -79, -80, -82, -85]) + (countLit q [-87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79, -80, -82, -85]) (l₂ := [-87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1311)) (literal (valuationOf q) (1319)) (countLit q [-75, -77, -79, -80, -82, -85]) (countLit q [-87, -88, -90, -93, -95, -96, -98]) (count1317 q) 1 2 (meaning1291 q) (meaning1311 q) (meaning1319 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1311 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1311 = false ∨ valuation q 1319 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1321 = true := by
  have hs : count1317 q = (countLit q [-75, -77, -79, -80, -82, -85]) + (countLit q [-87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79, -80, -82, -85]) (l₂ := [-87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1321)) (countLit q [-75, -77, -79, -80, -82, -85]) (countLit q [-87, -88, -90, -93, -95, -96, -98]) (count1317 q) 1 4 (meaning1291 q) (meaning1313 q) (meaning1321 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1313 = false ∨ valuation q 1321 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1310 = false ∨ valuationOf q 1319 = true := by
  have hs : count1317 q = (countLit q [-75, -77, -79, -80, -82, -85]) + (countLit q [-87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79, -80, -82, -85]) (l₂ := [-87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1292)) (literal (valuationOf q) (1310)) (literal (valuationOf q) (1319)) (countLit q [-75, -77, -79, -80, -82, -85]) (countLit q [-87, -88, -90, -93, -95, -96, -98]) (count1317 q) 2 1 (meaning1292 q) (meaning1310 q) (meaning1319 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1310 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1310 = false ∨ valuation q 1319 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1311 = false ∨ valuationOf q 1320 = true := by
  have hs : count1317 q = (countLit q [-75, -77, -79, -80, -82, -85]) + (countLit q [-87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79, -80, -82, -85]) (l₂ := [-87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1292)) (literal (valuationOf q) (1311)) (literal (valuationOf q) (1320)) (countLit q [-75, -77, -79, -80, -82, -85]) (countLit q [-87, -88, -90, -93, -95, -96, -98]) (count1317 q) 2 2 (meaning1292 q) (meaning1311 q) (meaning1320 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1311 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1311 = false ∨ valuation q 1320 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1310 = false ∨ valuationOf q 1320 = true := by
  have hs : count1317 q = (countLit q [-75, -77, -79, -80, -82, -85]) + (countLit q [-87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -79, -80, -82, -85]) (l₂ := [-87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1310)) (literal (valuationOf q) (1320)) (countLit q [-75, -77, -79, -80, -82, -85]) (countLit q [-87, -88, -90, -93, -95, -96, -98]) (count1317 q) 3 1 (meaning1293 q) (meaning1310 q) (meaning1320 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1310 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1310 = false ∨ valuation q 1320 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 1318 = false ∨ valuationOf q 1327 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_right (literal (valuationOf q) (1318)) (literal (valuationOf q) (1327)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 2 (meaning1318 q) (meaning1327 q) hs
  change valuationOf q 1318 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 1318 = false ∨ valuation q 1327 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1328 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_right (literal (valuationOf q) (1319)) (literal (valuationOf q) (1328)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 3 (meaning1319 q) (meaning1328 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1328 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1329 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_right (literal (valuationOf q) (1320)) (literal (valuationOf q) (1329)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 4 (meaning1320 q) (meaning1329 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1329 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1327 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1327)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 1 1 (meaning1272 q) (meaning1317 q) (meaning1327 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1317 = false ∨ valuation q 1327 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1328 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1318)) (literal (valuationOf q) (1328)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 1 2 (meaning1272 q) (meaning1318 q) (meaning1328 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1318 = false ∨ valuation q 1328 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1329 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1329)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 1 3 (meaning1272 q) (meaning1319 q) (meaning1329 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1319 = false ∨ valuation q 1329 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1330 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1330)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 1 4 (meaning1272 q) (meaning1320 q) (meaning1330 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1320 = false ∨ valuation q 1330 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1331 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1331)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 1 5 (meaning1272 q) (meaning1321 q) (meaning1331 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1321 = false ∨ valuation q 1331 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1328 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1328)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 2 1 (meaning1273 q) (meaning1317 q) (meaning1328 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1317 = false ∨ valuation q 1328 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1329 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1318)) (literal (valuationOf q) (1329)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 2 2 (meaning1273 q) (meaning1318 q) (meaning1329 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1318 = false ∨ valuation q 1329 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1330 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1330)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 2 3 (meaning1273 q) (meaning1319 q) (meaning1330 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1319 = false ∨ valuation q 1330 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1331 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1331)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 2 4 (meaning1273 q) (meaning1320 q) (meaning1331 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1320 = false ∨ valuation q 1331 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1329 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1329)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 3 1 (meaning1274 q) (meaning1317 q) (meaning1329 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1317 = false ∨ valuation q 1329 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1330 = true := by
  have hs : count1326 q = (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) + (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (l₂ := [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1318)) (literal (valuationOf q) (1330)) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73]) (countLit q [-75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1326 q) 3 2 (meaning1274 q) (meaning1318 q) (meaning1330 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1318 = false ∨ valuation q 1330 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1343 = true := by
  have hs : count1335 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) + (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (l₂ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1233)) (literal (valuationOf q) (1331)) (literal (valuationOf q) (1343)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1335 q) 3 6 (meaning1233 q) (meaning1331 q) (meaning1343 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1331 = false ∨ valuation q 1343 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 1234 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1343 = true := by
  have hs : count1335 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) + (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (l₂ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1234)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1343)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1335 q) 4 5 (meaning1234 q) (meaning1330 q) (meaning1343 q) hs
  change valuationOf q 1234 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 1234 = false ∨ valuation q 1330 = false ∨ valuation q 1343 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 1235 = false ∨ valuationOf q 1329 = false ∨ valuationOf q 1343 = true := by
  have hs : count1335 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) + (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (l₂ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1235)) (literal (valuationOf q) (1329)) (literal (valuationOf q) (1343)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1335 q) 5 4 (meaning1235 q) (meaning1329 q) (meaning1343 q) hs
  change valuationOf q 1235 = false ∨ valuationOf q 1329 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 1235 = false ∨ valuation q 1329 = false ∨ valuation q 1343 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 1236 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1343 = true := by
  have hs : count1335 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) + (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (l₂ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1236)) (literal (valuationOf q) (1328)) (literal (valuationOf q) (1343)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1335 q) 6 3 (meaning1236 q) (meaning1328 q) (meaning1343 q) hs
  change valuationOf q 1236 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 1236 = false ∨ valuation q 1328 = false ∨ valuation q 1343 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 1237 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1343 = true := by
  have hs : count1335 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) + (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (l₂ := [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1237)) (literal (valuationOf q) (1327)) (literal (valuationOf q) (1343)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23, -26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (countLit q [-50, -52, -56, -58, -59, -61, -64, -65, -67, -70, -72, -73, -75, -77, -79, -80, -82, -85, -87, -88, -90, -93, -95, -96, -98]) (count1335 q) 7 2 (meaning1237 q) (meaning1327 q) (meaning1343 q) hs
  change valuationOf q 1237 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 1237 = false ∨ valuation q 1327 = false ∨ valuation q 1343 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E170.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112170
