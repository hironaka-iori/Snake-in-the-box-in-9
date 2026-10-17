import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1493 = true := by
  have hs : count1483 q = (countLit q [-55, -57, -58, -62, -63, -67, -69]) + (countLit q [-70, -72, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69]) (l₂ := [-70, -72, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1493)) (countLit q [-55, -57, -58, -62, -63, -67, -69]) (countLit q [-70, -72, -74, -76, -78, -80, -81]) (count1483 q) 5 6 (meaning1460 q) (meaning1481 q) (meaning1493 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1481 = false ∨ valuation q 1493 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1497)) (countLit q [-87]) (countLit q [-88]) (count1497 q) 1 (meaningNeg88 q) (meaning1497 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1497 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1497)) (countLit q [-87]) (countLit q [-88]) (count1497 q) 1 (meaningNeg87 q) (meaning1497 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1497 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 88 = true ∨ valuationOf q 1498 = true := by
  have hs : count1497 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (1498)) (countLit q [-87]) (countLit q [-88]) (count1497 q) 1 1 (meaningNeg87 q) (meaningNeg88 q) (meaning1498 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 1498 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_right (literal (valuationOf q) (1497)) (literal (valuationOf q) (1499)) (countLit q [-85]) (countLit q [-87, -88]) (count1499 q) 1 (meaning1497 q) (meaning1499 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1499 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_right (literal (valuationOf q) (1498)) (literal (valuationOf q) (1500)) (countLit q [-85]) (countLit q [-87, -88]) (count1499 q) 2 (meaning1498 q) (meaning1500 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1500 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1499)) (countLit q [-85]) (countLit q [-87, -88]) (count1499 q) 1 (meaningNeg85 q) (meaning1499 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1499 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1497 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1500)) (countLit q [-85]) (countLit q [-87, -88]) (count1499 q) 1 1 (meaningNeg85 q) (meaning1497 q) (meaning1500 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1497 = false ∨ valuation q 1500 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1498 = false ∨ valuationOf q 1501 = true := by
  have hs : count1499 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1501)) (countLit q [-85]) (countLit q [-87, -88]) (count1499 q) 1 2 (meaningNeg85 q) (meaning1498 q) (meaning1501 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1498 = false ∨ valuation q 1501 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-90]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1502)) (countLit q [-90]) (countLit q [-93]) (count1502 q) 1 (meaningNeg93 q) (meaning1502 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1502 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-90]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1502)) (countLit q [-90]) (countLit q [-93]) (count1502 q) 1 (meaningNeg90 q) (meaning1502 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1502 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1503 = true := by
  have hs : count1502 q = (countLit q [-90]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1503)) (countLit q [-90]) (countLit q [-93]) (count1502 q) 1 1 (meaningNeg90 q) (meaningNeg93 q) (meaning1503 q) hs
  change (! (valuationOf q 90)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 93 = true ∨ valuation q 1503 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1504)) (countLit q [-95]) (countLit q [-97]) (count1504 q) 1 (meaningNeg97 q) (meaning1504 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1504 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1504)) (countLit q [-95]) (countLit q [-97]) (count1504 q) 1 (meaningNeg95 q) (meaning1504 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1504 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1505)) (countLit q [-95]) (countLit q [-97]) (count1504 q) 1 1 (meaningNeg95 q) (meaningNeg97 q) (meaning1505 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 1505 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-90, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-90, -93]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuationOf q) (1504)) (literal (valuationOf q) (1506)) (countLit q [-90, -93]) (countLit q [-95, -97]) (count1506 q) 1 (meaning1504 q) (meaning1506 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1506 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-90, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-90, -93]) (l₂ := [-95, -97])
  have hm := merge_left (literal (valuationOf q) (1502)) (literal (valuationOf q) (1506)) (countLit q [-90, -93]) (countLit q [-95, -97]) (count1506 q) 1 (meaning1502 q) (meaning1506 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1506 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-90, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-90, -93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1507)) (countLit q [-90, -93]) (countLit q [-95, -97]) (count1506 q) 1 1 (meaning1502 q) (meaning1504 q) (meaning1507 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = false ∨ valuation q 1507 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true := by
  have hs : count1506 q = (countLit q [-90, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-90, -93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1508)) (countLit q [-90, -93]) (countLit q [-95, -97]) (count1506 q) 1 2 (meaning1502 q) (meaning1505 q) (meaning1508 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1505 = false ∨ valuation q 1508 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-90, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-90, -93]) (l₂ := [-95, -97])
  have hm := merge_left (literal (valuationOf q) (1503)) (literal (valuationOf q) (1507)) (countLit q [-90, -93]) (countLit q [-95, -97]) (count1506 q) 2 (meaning1503 q) (meaning1507 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1507 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1508 = true := by
  have hs : count1506 q = (countLit q [-90, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-90, -93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1508)) (countLit q [-90, -93]) (countLit q [-95, -97]) (count1506 q) 2 1 (meaning1503 q) (meaning1504 q) (meaning1508 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1504 = false ∨ valuation q 1508 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_right (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 1 (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1510 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_right (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 2 (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1511 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_left (literal (valuationOf q) (1499)) (literal (valuationOf q) (1510)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 1 (meaning1499 q) (meaning1510 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1510 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1511)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 1 1 (meaning1499 q) (meaning1506 q) (meaning1511 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1506 = false ∨ valuation q 1511 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1512)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 1 2 (meaning1499 q) (meaning1507 q) (meaning1512 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1507 = false ∨ valuation q 1512 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1513)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 1 3 (meaning1499 q) (meaning1508 q) (meaning1513 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1508 = false ∨ valuation q 1513 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_left (literal (valuationOf q) (1500)) (literal (valuationOf q) (1511)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 2 (meaning1500 q) (meaning1511 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1511 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1512)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 2 1 (meaning1500 q) (meaning1506 q) (meaning1512 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1506 = false ∨ valuation q 1512 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1513)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 2 2 (meaning1500 q) (meaning1507 q) (meaning1513 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1507 = false ∨ valuation q 1513 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 2 3 (meaning1500 q) (meaning1508 q) (meaning1514 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1508 = false ∨ valuation q 1514 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_left (literal (valuationOf q) (1501)) (literal (valuationOf q) (1512)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 3 (meaning1501 q) (meaning1512 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1512 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E161.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112161
