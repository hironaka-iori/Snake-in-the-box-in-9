import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1550 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1550)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 1 2 (meaning1537 q) (meaning1545 q) (meaning1550 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1545 = false ∨ valuation q 1550 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1551 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1551)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 1 3 (meaning1537 q) (meaning1546 q) (meaning1551 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1546 = false ∨ valuation q 1551 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1552 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1552)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 1 4 (meaning1537 q) (meaning1547 q) (meaning1552 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1547 = false ∨ valuation q 1552 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1549 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_left (literal (valuationOf q) (1538)) (literal (valuationOf q) (1549)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 2 (meaning1538 q) (meaning1549 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1549 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1550 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1550)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 2 1 (meaning1538 q) (meaning1544 q) (meaning1550 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1544 = false ∨ valuation q 1550 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1551 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1551)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 2 2 (meaning1538 q) (meaning1545 q) (meaning1551 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1545 = false ∨ valuation q 1551 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1552 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1552)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 2 3 (meaning1538 q) (meaning1546 q) (meaning1552 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1546 = false ∨ valuation q 1552 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1553 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1553)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 2 4 (meaning1538 q) (meaning1547 q) (meaning1553 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1547 = false ∨ valuation q 1553 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1550 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_left (literal (valuationOf q) (1539)) (literal (valuationOf q) (1550)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 3 (meaning1539 q) (meaning1550 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1550 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1551 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1551)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 3 1 (meaning1539 q) (meaning1544 q) (meaning1551 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1544 = false ∨ valuation q 1551 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1552 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1552)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 3 2 (meaning1539 q) (meaning1545 q) (meaning1552 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1545 = false ∨ valuation q 1552 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1553 = true := by
  have hs : count1548 q = (countLit q [-59, -60, -62]) + (countLit q [-65, -66, -68, -70]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62]) (l₂ := [-65, -66, -68, -70])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1553)) (countLit q [-59, -60, -62]) (countLit q [-65, -66, -68, -70]) (count1548 q) 3 3 (meaning1539 q) (meaning1546 q) (meaning1553 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1546 = false ∨ valuation q 1553 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1555)) (countLit q [-72]) (countLit q [-74]) (count1555 q) 1 (meaningNeg74 q) (meaning1555 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1555 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1555)) (countLit q [-72]) (countLit q [-74]) (count1555 q) 1 (meaningNeg72 q) (meaning1555 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1555 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1556)) (countLit q [-72]) (countLit q [-74]) (count1555 q) 1 1 (meaningNeg72 q) (meaningNeg74 q) (meaning1556 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 74 = true ∨ valuation q 1556 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1557)) (countLit q [-76]) (countLit q [-78]) (count1557 q) 1 (meaningNeg78 q) (meaning1557 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1557 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1557)) (countLit q [-76]) (countLit q [-78]) (count1557 q) 1 (meaningNeg76 q) (meaning1557 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1557 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 78 = true ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (1558)) (countLit q [-76]) (countLit q [-78]) (count1557 q) 1 1 (meaningNeg76 q) (meaningNeg78 q) (meaning1558 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 1558 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1559 = true := by
  have hs : count1559 q = (countLit q [-72, -74]) + (countLit q [-76, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -78])
  have hm := merge_right (literal (valuationOf q) (1557)) (literal (valuationOf q) (1559)) (countLit q [-72, -74]) (countLit q [-76, -78]) (count1559 q) 1 (meaning1557 q) (meaning1559 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1559 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-72, -74]) + (countLit q [-76, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -78])
  have hm := merge_right (literal (valuationOf q) (1558)) (literal (valuationOf q) (1560)) (countLit q [-72, -74]) (countLit q [-76, -78]) (count1559 q) 2 (meaning1558 q) (meaning1560 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1560 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1559 = true := by
  have hs : count1559 q = (countLit q [-72, -74]) + (countLit q [-76, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -78])
  have hm := merge_left (literal (valuationOf q) (1555)) (literal (valuationOf q) (1559)) (countLit q [-72, -74]) (countLit q [-76, -78]) (count1559 q) 1 (meaning1555 q) (meaning1559 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1559 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-72, -74]) + (countLit q [-76, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -78])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1560)) (countLit q [-72, -74]) (countLit q [-76, -78]) (count1559 q) 1 1 (meaning1555 q) (meaning1557 q) (meaning1560 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1557 = false ∨ valuation q 1560 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-72, -74]) + (countLit q [-76, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -78])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1561)) (countLit q [-72, -74]) (countLit q [-76, -78]) (count1559 q) 1 2 (meaning1555 q) (meaning1558 q) (meaning1561 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1558 = false ∨ valuation q 1561 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-72, -74]) + (countLit q [-76, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -78])
  have hm := merge_left (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-72, -74]) (countLit q [-76, -78]) (count1559 q) 2 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-72, -74]) + (countLit q [-76, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -78])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1561)) (countLit q [-72, -74]) (countLit q [-76, -78]) (count1559 q) 2 1 (meaning1556 q) (meaning1557 q) (meaning1561 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1557 = false ∨ valuation q 1561 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true := by
  have hs : count1559 q = (countLit q [-72, -74]) + (countLit q [-76, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -78])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1562)) (countLit q [-72, -74]) (countLit q [-76, -78]) (count1559 q) 2 2 (meaning1556 q) (meaning1558 q) (meaning1562 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = false ∨ valuation q 1562 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1563 = true := by
  have hs : count1563 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1563)) (countLit q [-81]) (countLit q [-82]) (count1563 q) 1 (meaningNeg82 q) (meaning1563 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1563 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1563 = true := by
  have hs : count1563 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1563)) (countLit q [-81]) (countLit q [-82]) (count1563 q) 1 (meaningNeg81 q) (meaning1563 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1563 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1564 = true := by
  have hs : count1563 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1564)) (countLit q [-81]) (countLit q [-82]) (count1563 q) 1 1 (meaningNeg81 q) (meaningNeg82 q) (meaning1564 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 1564 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1565 = true := by
  have hs : count1565 q = (countLit q [-83]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1565)) (countLit q [-83]) (countLit q [-86]) (count1565 q) 1 (meaningNeg86 q) (meaning1565 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1565 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1565 = true := by
  have hs : count1565 q = (countLit q [-83]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1565)) (countLit q [-83]) (countLit q [-86]) (count1565 q) 1 (meaningNeg83 q) (meaning1565 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1565 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1566 = true := by
  have hs : count1565 q = (countLit q [-83]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1566)) (countLit q [-83]) (countLit q [-86]) (count1565 q) 1 1 (meaningNeg83 q) (meaningNeg86 q) (meaning1566 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 1566 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E064.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112064
