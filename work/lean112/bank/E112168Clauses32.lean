import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-93, -94]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-98, -100])
  have hm := merge_left (literal (valuationOf q) (1557)) (literal (valuationOf q) (1561)) (countLit q [-93, -94]) (countLit q [-98, -100]) (count1560 q) 2 (meaning1557 q) (meaning1561 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1561 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true := by
  have hs : count1560 q = (countLit q [-93, -94]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1562)) (countLit q [-93, -94]) (countLit q [-98, -100]) (count1560 q) 2 1 (meaning1557 q) (meaning1558 q) (meaning1562 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1558 = false ∨ valuation q 1562 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-87, -91, -92]) + (countLit q [-93, -94, -98, -100]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92]) (l₂ := [-93, -94, -98, -100])
  have hm := merge_right (literal (valuationOf q) (1560)) (literal (valuationOf q) (1564)) (countLit q [-87, -91, -92]) (countLit q [-93, -94, -98, -100]) (count1564 q) 1 (meaning1560 q) (meaning1564 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1564 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-87, -91, -92]) + (countLit q [-93, -94, -98, -100]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92]) (l₂ := [-93, -94, -98, -100])
  have hm := merge_right (literal (valuationOf q) (1561)) (literal (valuationOf q) (1565)) (countLit q [-87, -91, -92]) (countLit q [-93, -94, -98, -100]) (count1564 q) 2 (meaning1561 q) (meaning1565 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1565 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-87, -91, -92]) + (countLit q [-93, -94, -98, -100]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92]) (l₂ := [-93, -94, -98, -100])
  have hm := merge_right (literal (valuationOf q) (1562)) (literal (valuationOf q) (1566)) (countLit q [-87, -91, -92]) (countLit q [-93, -94, -98, -100]) (count1564 q) 3 (meaning1562 q) (meaning1566 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1566 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-87, -91, -92]) + (countLit q [-93, -94, -98, -100]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92]) (l₂ := [-93, -94, -98, -100])
  have hm := merge_left (literal (valuationOf q) (1553)) (literal (valuationOf q) (1564)) (countLit q [-87, -91, -92]) (countLit q [-93, -94, -98, -100]) (count1564 q) 1 (meaning1553 q) (meaning1564 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1564 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-87, -91, -92]) + (countLit q [-93, -94, -98, -100]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92]) (l₂ := [-93, -94, -98, -100])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1565)) (countLit q [-87, -91, -92]) (countLit q [-93, -94, -98, -100]) (count1564 q) 1 1 (meaning1553 q) (meaning1560 q) (meaning1565 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1560 = false ∨ valuation q 1565 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-87, -91, -92]) + (countLit q [-93, -94, -98, -100]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92]) (l₂ := [-93, -94, -98, -100])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1566)) (countLit q [-87, -91, -92]) (countLit q [-93, -94, -98, -100]) (count1564 q) 1 2 (meaning1553 q) (meaning1561 q) (meaning1566 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1561 = false ∨ valuation q 1566 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1567 = true := by
  have hs : count1564 q = (countLit q [-87, -91, -92]) + (countLit q [-93, -94, -98, -100]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92]) (l₂ := [-93, -94, -98, -100])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1567)) (countLit q [-87, -91, -92]) (countLit q [-93, -94, -98, -100]) (count1564 q) 1 3 (meaning1553 q) (meaning1562 q) (meaning1567 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1562 = false ∨ valuation q 1567 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-87, -91, -92]) + (countLit q [-93, -94, -98, -100]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92]) (l₂ := [-93, -94, -98, -100])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1566)) (countLit q [-87, -91, -92]) (countLit q [-93, -94, -98, -100]) (count1564 q) 2 1 (meaning1554 q) (meaning1560 q) (meaning1566 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1560 = false ∨ valuation q 1566 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1567 = true := by
  have hs : count1564 q = (countLit q [-87, -91, -92]) + (countLit q [-93, -94, -98, -100]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92]) (l₂ := [-93, -94, -98, -100])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1567)) (countLit q [-87, -91, -92]) (countLit q [-93, -94, -98, -100]) (count1564 q) 2 2 (meaning1554 q) (meaning1561 q) (meaning1567 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1561 = false ∨ valuation q 1567 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-87, -91, -92]) + (countLit q [-93, -94, -98, -100]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92]) (l₂ := [-93, -94, -98, -100])
  have hm := merge_left (literal (valuationOf q) (1555)) (literal (valuationOf q) (1566)) (countLit q [-87, -91, -92]) (countLit q [-93, -94, -98, -100]) (count1564 q) 3 (meaning1555 q) (meaning1566 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1566 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1571)) (countLit q [-102]) (countLit q [-104]) (count1571 q) 1 (meaningNeg104 q) (meaning1571 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1571 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1571)) (countLit q [-102]) (countLit q [-104]) (count1571 q) 1 (meaningNeg102 q) (meaning1571 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1571 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 104 = true ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-104)) (literal (valuationOf q) (1572)) (countLit q [-102]) (countLit q [-104]) (count1571 q) 1 1 (meaningNeg102 q) (meaningNeg104 q) (meaning1572 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 104)) = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 104 = true ∨ valuation q 1572 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-101]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102, -104])
  have hm := merge_right (literal (valuationOf q) (1571)) (literal (valuationOf q) (1573)) (countLit q [-101]) (countLit q [-102, -104]) (count1573 q) 1 (meaning1571 q) (meaning1573 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1573 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1574 = true := by
  have hs : count1573 q = (countLit q [-101]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102, -104])
  have hm := merge_right (literal (valuationOf q) (1572)) (literal (valuationOf q) (1574)) (countLit q [-101]) (countLit q [-102, -104]) (count1573 q) 2 (meaning1572 q) (meaning1574 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1574 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-101]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102, -104])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1573)) (countLit q [-101]) (countLit q [-102, -104]) (count1573 q) 1 (meaningNeg101 q) (meaning1573 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1573 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1571 = false ∨ valuationOf q 1574 = true := by
  have hs : count1573 q = (countLit q [-101]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102, -104])
  have hm := merge_two (literal (valuationOf q) (-101)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1574)) (countLit q [-101]) (countLit q [-102, -104]) (count1573 q) 1 1 (meaningNeg101 q) (meaning1571 q) (meaning1574 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1571 = false ∨ valuation q 1574 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1572 = false ∨ valuationOf q 1575 = true := by
  have hs : count1573 q = (countLit q [-101]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102, -104])
  have hm := merge_two (literal (valuationOf q) (-101)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1575)) (countLit q [-101]) (countLit q [-102, -104]) (count1573 q) 1 2 (meaningNeg101 q) (meaning1572 q) (meaning1575 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1572 = false ∨ valuation q 1575 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-107]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (1576)) (countLit q [-107]) (countLit q [-110]) (count1576 q) 1 (meaningNeg110 q) (meaning1576 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1576 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-107]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1576)) (countLit q [-107]) (countLit q [-110]) (count1576 q) 1 (meaningNeg107 q) (meaning1576 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1576 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1578)) (countLit q [-111]) (countLit q [-113]) (count1578 q) 1 (meaningNeg113 q) (meaning1578 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1578 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1578)) (countLit q [-111]) (countLit q [-113]) (count1578 q) 1 (meaningNeg111 q) (meaning1578 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1578 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1579 = true := by
  have hs : count1578 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1579)) (countLit q [-111]) (countLit q [-113]) (count1578 q) 1 1 (meaningNeg111 q) (meaningNeg113 q) (meaning1579 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 1579 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-107, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -110]) (l₂ := [-111, -113])
  have hm := merge_right (literal (valuationOf q) (1578)) (literal (valuationOf q) (1580)) (countLit q [-107, -110]) (countLit q [-111, -113]) (count1580 q) 1 (meaning1578 q) (meaning1580 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1580 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-107, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -110]) (l₂ := [-111, -113])
  have hm := merge_right (literal (valuationOf q) (1579)) (literal (valuationOf q) (1581)) (countLit q [-107, -110]) (countLit q [-111, -113]) (count1580 q) 2 (meaning1579 q) (meaning1581 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1581 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-107, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -110]) (l₂ := [-111, -113])
  have hm := merge_left (literal (valuationOf q) (1576)) (literal (valuationOf q) (1580)) (countLit q [-107, -110]) (countLit q [-111, -113]) (count1580 q) 1 (meaning1576 q) (meaning1580 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1580 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-107, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -110]) (l₂ := [-111, -113])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1581)) (countLit q [-107, -110]) (countLit q [-111, -113]) (count1580 q) 1 1 (meaning1576 q) (meaning1578 q) (meaning1581 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1578 = false ∨ valuation q 1581 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1584 = true := by
  have hs : count1584 q = (countLit q [-101, -102, -104]) + (countLit q [-107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-101, -102, -104]) (l₂ := [-107, -110, -111, -113])
  have hm := merge_right (literal (valuationOf q) (1580)) (literal (valuationOf q) (1584)) (countLit q [-101, -102, -104]) (countLit q [-107, -110, -111, -113]) (count1584 q) 1 (meaning1580 q) (meaning1584 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1584 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-101, -102, -104]) + (countLit q [-107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-101, -102, -104]) (l₂ := [-107, -110, -111, -113])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-101, -102, -104]) (countLit q [-107, -110, -111, -113]) (count1584 q) 2 (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1585 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1584 = true := by
  have hs : count1584 q = (countLit q [-101, -102, -104]) + (countLit q [-107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-101, -102, -104]) (l₂ := [-107, -110, -111, -113])
  have hm := merge_left (literal (valuationOf q) (1573)) (literal (valuationOf q) (1584)) (countLit q [-101, -102, -104]) (countLit q [-107, -110, -111, -113]) (count1584 q) 1 (meaning1573 q) (meaning1584 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1584 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E168.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112168
