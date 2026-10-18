import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1513 = true := by
  have hs : count1509 q = (countLit q [-30, -31, -35, -37, -38, -39, -43]) + (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -37, -38, -39, -43]) (l₂ := [-45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1513)) (countLit q [-30, -31, -35, -37, -38, -39, -43]) (countLit q [-45, -49, -50, -53, -55, -57, -58, -60]) (count1509 q) 3 2 (meaning1480 q) (meaning1502 q) (meaning1513 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1502 = false ∨ valuation q 1513 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1536 = true := by
  have hs : count1524 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) + (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (l₂ := [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1536)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]) (countLit q [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (count1524 q) 8 5 (meaning1458 q) (meaning1513 q) (meaning1536 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1513 = false ∨ valuation q 1536 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1542 = true := by
  have hs : count1542 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1542)) (countLit q [-63]) (countLit q [-66]) (count1542 q) 1 (meaningNeg66 q) (meaning1542 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1542 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1542 = true := by
  have hs : count1542 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1542)) (countLit q [-63]) (countLit q [-66]) (count1542 q) 1 (meaningNeg63 q) (meaning1542 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1542 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1544 = true := by
  have hs : count1544 q = (countLit q [-62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -66])
  have hm := merge_right (literal (valuationOf q) (1542)) (literal (valuationOf q) (1544)) (countLit q [-62]) (countLit q [-63, -66]) (count1544 q) 1 (meaning1542 q) (meaning1544 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1544 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1547)) (countLit q [-69]) (countLit q [-71]) (count1547 q) 1 (meaningNeg71 q) (meaning1547 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1547 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1547)) (countLit q [-69]) (countLit q [-71]) (count1547 q) 1 (meaningNeg69 q) (meaning1547 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1547 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1549)) (countLit q [-72]) (countLit q [-74]) (count1549 q) 1 (meaningNeg74 q) (meaning1549 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1549 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1549)) (countLit q [-72]) (countLit q [-74]) (count1549 q) 1 (meaningNeg72 q) (meaning1549 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1549 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-69, -71]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -71]) (l₂ := [-72, -74])
  have hm := merge_right (literal (valuationOf q) (1549)) (literal (valuationOf q) (1551)) (countLit q [-69, -71]) (countLit q [-72, -74]) (count1551 q) 1 (meaning1549 q) (meaning1551 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1551 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-69, -71]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -71]) (l₂ := [-72, -74])
  have hm := merge_left (literal (valuationOf q) (1547)) (literal (valuationOf q) (1551)) (countLit q [-69, -71]) (countLit q [-72, -74]) (count1551 q) 1 (meaning1547 q) (meaning1551 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1551 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-62, -63, -66]) + (countLit q [-69, -71, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66]) (l₂ := [-69, -71, -72, -74])
  have hm := merge_right (literal (valuationOf q) (1551)) (literal (valuationOf q) (1555)) (countLit q [-62, -63, -66]) (countLit q [-69, -71, -72, -74]) (count1555 q) 1 (meaning1551 q) (meaning1555 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1555 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-62, -63, -66]) + (countLit q [-69, -71, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66]) (l₂ := [-69, -71, -72, -74])
  have hm := merge_left (literal (valuationOf q) (1544)) (literal (valuationOf q) (1555)) (countLit q [-62, -63, -66]) (countLit q [-69, -71, -72, -74]) (count1555 q) 1 (meaning1544 q) (meaning1555 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1555 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-62, -63, -66]) + (countLit q [-69, -71, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66]) (l₂ := [-69, -71, -72, -74])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1556)) (countLit q [-62, -63, -66]) (countLit q [-69, -71, -72, -74]) (count1555 q) 1 1 (meaning1544 q) (meaning1551 q) (meaning1556 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1551 = false ∨ valuation q 1556 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-79]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1562)) (countLit q [-79]) (countLit q [-81]) (count1562 q) 1 (meaningNeg81 q) (meaning1562 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1562 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-79]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1562)) (countLit q [-79]) (countLit q [-81]) (count1562 q) 1 (meaningNeg79 q) (meaning1562 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1562 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-75]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-79, -81])
  have hm := merge_right (literal (valuationOf q) (1562)) (literal (valuationOf q) (1564)) (countLit q [-75]) (countLit q [-79, -81]) (count1564 q) 1 (meaning1562 q) (meaning1564 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1564 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-75]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-79, -81])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1564)) (countLit q [-75]) (countLit q [-79, -81]) (count1564 q) 1 (meaningNeg75 q) (meaning1564 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1564 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1562 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-75]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-79, -81])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1565)) (countLit q [-75]) (countLit q [-79, -81]) (count1564 q) 1 1 (meaningNeg75 q) (meaning1562 q) (meaning1565 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1562 = false ∨ valuation q 1565 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1567 = true := by
  have hs : count1567 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (1567)) (countLit q [-82]) (countLit q [-83]) (count1567 q) 1 (meaningNeg83 q) (meaning1567 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1567 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1567 = true := by
  have hs : count1567 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1567)) (countLit q [-82]) (countLit q [-83]) (count1567 q) 1 (meaningNeg82 q) (meaning1567 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1567 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-82, -83]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-87, -89])
  have hm := merge_left (literal (valuationOf q) (1567)) (literal (valuationOf q) (1571)) (countLit q [-82, -83]) (countLit q [-87, -89]) (count1571 q) 1 (meaning1567 q) (meaning1571 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1571 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-75, -79, -81]) + (countLit q [-82, -83, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -81]) (l₂ := [-82, -83, -87, -89])
  have hm := merge_right (literal (valuationOf q) (1571)) (literal (valuationOf q) (1575)) (countLit q [-75, -79, -81]) (countLit q [-82, -83, -87, -89]) (count1575 q) 1 (meaning1571 q) (meaning1575 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1575 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-75, -79, -81]) + (countLit q [-82, -83, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -81]) (l₂ := [-82, -83, -87, -89])
  have hm := merge_left (literal (valuationOf q) (1564)) (literal (valuationOf q) (1575)) (countLit q [-75, -79, -81]) (countLit q [-82, -83, -87, -89]) (count1575 q) 1 (meaning1564 q) (meaning1575 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1575 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-75, -79, -81]) + (countLit q [-82, -83, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -81]) (l₂ := [-82, -83, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1576)) (countLit q [-75, -79, -81]) (countLit q [-82, -83, -87, -89]) (count1575 q) 1 1 (meaning1564 q) (meaning1571 q) (meaning1576 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1571 = false ∨ valuation q 1576 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-75, -79, -81]) + (countLit q [-82, -83, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -81]) (l₂ := [-82, -83, -87, -89])
  have hm := merge_left (literal (valuationOf q) (1565)) (literal (valuationOf q) (1576)) (countLit q [-75, -79, -81]) (countLit q [-82, -83, -87, -89]) (count1575 q) 2 (meaning1565 q) (meaning1576 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1576 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -81, -82, -83, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -81, -82, -83, -87, -89])
  have hm := merge_right (literal (valuationOf q) (1576)) (literal (valuationOf q) (1583)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -81, -82, -83, -87, -89]) (count1582 q) 2 (meaning1576 q) (meaning1583 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1583 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -81, -82, -83, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -81, -82, -83, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1583)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -81, -82, -83, -87, -89]) (count1582 q) 1 1 (meaning1555 q) (meaning1575 q) (meaning1583 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1575 = false ∨ valuation q 1583 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -81, -82, -83, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -81, -82, -83, -87, -89])
  have hm := merge_left (literal (valuationOf q) (1556)) (literal (valuationOf q) (1583)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -81, -82, -83, -87, -89]) (count1582 q) 2 (meaning1556 q) (meaning1583 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1583 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1601 = true := by
  have hs : count1601 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1601)) (countLit q [-95]) (countLit q [-98]) (count1601 q) 1 (meaningNeg98 q) (meaning1601 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1601 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1601 = true := by
  have hs : count1601 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1601)) (countLit q [-95]) (countLit q [-98]) (count1601 q) 1 (meaningNeg95 q) (meaning1601 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1601 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1603 = true := by
  have hs : count1603 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1603)) (countLit q [-99]) (countLit q [-100]) (count1603 q) 1 (meaningNeg100 q) (meaning1603 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1603 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E203.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112203
