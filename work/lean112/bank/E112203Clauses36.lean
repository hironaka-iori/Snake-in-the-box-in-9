import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-15]) + (countLit q [-18, -21]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18, -21])
  have hm := merge_right (literal (valuationOf q) (1431)) (literal (valuationOf q) (1433)) (countLit q [-15]) (countLit q [-18, -21]) (count1433 q) 1 (meaning1431 q) (meaning1433 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1433 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1438)) (countLit q [-25]) (countLit q [-27]) (count1438 q) 1 (meaningNeg25 q) (meaning1438 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1438 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1440 = true := by
  have hs : count1440 q = (countLit q [-22, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-25, -27])
  have hm := merge_right (literal (valuationOf q) (1438)) (literal (valuationOf q) (1440)) (countLit q [-22, -23]) (countLit q [-25, -27]) (count1440 q) 1 (meaning1438 q) (meaning1440 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1440 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1445 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1445)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 1 1 (meaning1433 q) (meaning1440 q) (meaning1445 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1440 = false ∨ valuation q 1445 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1458 = true := by
  have hs : count1451 q = (countLit q [-2, -4, -5, -6, -10, -11, -12]) + (countLit q [-15, -18, -21, -22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12]) (l₂ := [-15, -18, -21, -22, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1458)) (countLit q [-2, -4, -5, -6, -10, -11, -12]) (countLit q [-15, -18, -21, -22, -23, -25, -27]) (count1451 q) 6 2 (meaning1429 q) (meaning1445 q) (meaning1458 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1445 = false ∨ valuation q 1458 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-31]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1465)) (countLit q [-31]) (countLit q [-35]) (count1465 q) 1 (meaningNeg35 q) (meaning1465 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1465 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-30]) + (countLit q [-31, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -35])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1468)) (countLit q [-30]) (countLit q [-31, -35]) (count1467 q) 1 1 (meaningNeg30 q) (meaning1465 q) (meaning1468 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1465 = false ∨ valuation q 1468 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (1470)) (countLit q [-37]) (countLit q [-38]) (count1470 q) 1 (meaningNeg38 q) (meaning1470 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1470 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1470)) (countLit q [-37]) (countLit q [-38]) (count1470 q) 1 (meaningNeg37 q) (meaning1470 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1470 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-39]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-43])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1472)) (countLit q [-39]) (countLit q [-43]) (count1472 q) 1 (meaningNeg39 q) (meaning1472 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1472 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-37, -38]) + (countLit q [-39, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-39, -43])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (countLit q [-37, -38]) (countLit q [-39, -43]) (count1474 q) 1 (meaning1472 q) (meaning1474 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-37, -38]) + (countLit q [-39, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-39, -43])
  have hm := merge_left (literal (valuationOf q) (1470)) (literal (valuationOf q) (1474)) (countLit q [-37, -38]) (countLit q [-39, -43]) (count1474 q) 1 (meaning1470 q) (meaning1474 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1474 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-30, -31, -35]) + (countLit q [-37, -38, -39, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-37, -38, -39, -43])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1480)) (countLit q [-30, -31, -35]) (countLit q [-37, -38, -39, -43]) (count1478 q) 2 1 (meaning1468 q) (meaning1474 q) (meaning1480 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1474 = false ∨ valuation q 1480 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-45]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1485)) (countLit q [-45]) (countLit q [-49]) (count1485 q) 1 (meaningNeg49 q) (meaning1485 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1485 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-45]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1485)) (countLit q [-45]) (countLit q [-49]) (count1485 q) 1 (meaningNeg45 q) (meaning1485 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1485 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 49 = true ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-45]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (1486)) (countLit q [-45]) (countLit q [-49]) (count1485 q) 1 1 (meaningNeg45 q) (meaningNeg49 q) (meaning1486 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 49 = true ∨ valuation q 1486 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-50]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (1487)) (countLit q [-50]) (countLit q [-53]) (count1487 q) 1 (meaningNeg53 q) (meaning1487 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1487 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-50]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1487)) (countLit q [-50]) (countLit q [-53]) (count1487 q) 1 (meaningNeg50 q) (meaning1487 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1487 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1489 = true := by
  have hs : count1489 q = (countLit q [-45, -49]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-50, -53])
  have hm := merge_right (literal (valuationOf q) (1487)) (literal (valuationOf q) (1489)) (countLit q [-45, -49]) (countLit q [-50, -53]) (count1489 q) 1 (meaning1487 q) (meaning1489 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1489 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1489 = true := by
  have hs : count1489 q = (countLit q [-45, -49]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-50, -53])
  have hm := merge_left (literal (valuationOf q) (1485)) (literal (valuationOf q) (1489)) (countLit q [-45, -49]) (countLit q [-50, -53]) (count1489 q) 1 (meaning1485 q) (meaning1489 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1489 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1490 = true := by
  have hs : count1489 q = (countLit q [-45, -49]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-50, -53])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1490)) (countLit q [-45, -49]) (countLit q [-50, -53]) (count1489 q) 1 1 (meaning1485 q) (meaning1487 q) (meaning1490 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1487 = false ∨ valuation q 1490 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1490 = true := by
  have hs : count1489 q = (countLit q [-45, -49]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-50, -53])
  have hm := merge_left (literal (valuationOf q) (1486)) (literal (valuationOf q) (1490)) (countLit q [-45, -49]) (countLit q [-50, -53]) (count1489 q) 2 (meaning1486 q) (meaning1490 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1490 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1493 = true := by
  have hs : count1493 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1493)) (countLit q [-55]) (countLit q [-57]) (count1493 q) 1 (meaningNeg57 q) (meaning1493 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1493 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1493 = true := by
  have hs : count1493 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1493)) (countLit q [-55]) (countLit q [-57]) (count1493 q) 1 (meaningNeg55 q) (meaning1493 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1493 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1495 = true := by
  have hs : count1495 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (1495)) (countLit q [-58]) (countLit q [-60]) (count1495 q) 1 (meaningNeg60 q) (meaning1495 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1495 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1495 = true := by
  have hs : count1495 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1495)) (countLit q [-58]) (countLit q [-60]) (count1495 q) 1 (meaningNeg58 q) (meaning1495 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1495 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-55, -57]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -60])
  have hm := merge_right (literal (valuationOf q) (1495)) (literal (valuationOf q) (1497)) (countLit q [-55, -57]) (countLit q [-58, -60]) (count1497 q) 1 (meaning1495 q) (meaning1497 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1497 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-55, -57]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -60])
  have hm := merge_left (literal (valuationOf q) (1493)) (literal (valuationOf q) (1497)) (countLit q [-55, -57]) (countLit q [-58, -60]) (count1497 q) 1 (meaning1493 q) (meaning1497 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1497 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1498 = true := by
  have hs : count1497 q = (countLit q [-55, -57]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -60])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1495)) (literal (valuationOf q) (1498)) (countLit q [-55, -57]) (countLit q [-58, -60]) (count1497 q) 1 1 (meaning1493 q) (meaning1495 q) (meaning1498 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1495 = false ∨ valuation q 1498 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-45, -49, -50, -53]) + (countLit q [-55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -50, -53]) (l₂ := [-55, -57, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1498)) (literal (valuationOf q) (1502)) (countLit q [-45, -49, -50, -53]) (countLit q [-55, -57, -58, -60]) (count1501 q) 2 (meaning1498 q) (meaning1502 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1502 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-45, -49, -50, -53]) + (countLit q [-55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -50, -53]) (l₂ := [-55, -57, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1502)) (countLit q [-45, -49, -50, -53]) (countLit q [-55, -57, -58, -60]) (count1501 q) 1 1 (meaning1489 q) (meaning1497 q) (meaning1502 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1497 = false ∨ valuation q 1502 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-45, -49, -50, -53]) + (countLit q [-55, -57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -50, -53]) (l₂ := [-55, -57, -58, -60])
  have hm := merge_left (literal (valuationOf q) (1490)) (literal (valuationOf q) (1502)) (countLit q [-45, -49, -50, -53]) (countLit q [-55, -57, -58, -60]) (count1501 q) 2 (meaning1490 q) (meaning1502 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1502 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E203.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112203
