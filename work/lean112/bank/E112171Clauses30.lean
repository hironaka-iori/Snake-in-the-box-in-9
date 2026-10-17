import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-93, -94]) + (countLit q [-95, -96]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-95, -96])
  have hm := merge_left (literal (valuationOf q) (1550)) (literal (valuationOf q) (1554)) (countLit q [-93, -94]) (countLit q [-95, -96]) (count1553 q) 2 (meaning1550 q) (meaning1554 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1554 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-86, -88, -89]) + (countLit q [-93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89]) (l₂ := [-93, -94, -95, -96])
  have hm := merge_right (literal (valuationOf q) (1553)) (literal (valuationOf q) (1557)) (countLit q [-86, -88, -89]) (countLit q [-93, -94, -95, -96]) (count1557 q) 1 (meaning1553 q) (meaning1557 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1557 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-86, -88, -89]) + (countLit q [-93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89]) (l₂ := [-93, -94, -95, -96])
  have hm := merge_right (literal (valuationOf q) (1554)) (literal (valuationOf q) (1558)) (countLit q [-86, -88, -89]) (countLit q [-93, -94, -95, -96]) (count1557 q) 2 (meaning1554 q) (meaning1558 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1558 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-86, -88, -89]) + (countLit q [-93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89]) (l₂ := [-93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1558)) (countLit q [-86, -88, -89]) (countLit q [-93, -94, -95, -96]) (count1557 q) 1 1 (meaning1546 q) (meaning1553 q) (meaning1558 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1553 = false ∨ valuation q 1558 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1559 = true := by
  have hs : count1557 q = (countLit q [-86, -88, -89]) + (countLit q [-93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89]) (l₂ := [-93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1559)) (countLit q [-86, -88, -89]) (countLit q [-93, -94, -95, -96]) (count1557 q) 1 2 (meaning1546 q) (meaning1554 q) (meaning1559 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1554 = false ∨ valuation q 1559 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-86, -88, -89]) + (countLit q [-93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89]) (l₂ := [-93, -94, -95, -96])
  have hm := merge_left (literal (valuationOf q) (1547)) (literal (valuationOf q) (1558)) (countLit q [-86, -88, -89]) (countLit q [-93, -94, -95, -96]) (count1557 q) 2 (meaning1547 q) (meaning1558 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1558 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1559 = true := by
  have hs : count1557 q = (countLit q [-86, -88, -89]) + (countLit q [-93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89]) (l₂ := [-93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1559)) (countLit q [-86, -88, -89]) (countLit q [-93, -94, -95, -96]) (count1557 q) 2 1 (meaning1547 q) (meaning1553 q) (meaning1559 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1553 = false ∨ valuation q 1559 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1560 = true := by
  have hs : count1557 q = (countLit q [-86, -88, -89]) + (countLit q [-93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89]) (l₂ := [-93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1560)) (countLit q [-86, -88, -89]) (countLit q [-93, -94, -95, -96]) (count1557 q) 2 2 (meaning1547 q) (meaning1554 q) (meaning1560 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1554 = false ∨ valuation q 1560 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1560 = true := by
  have hs : count1557 q = (countLit q [-86, -88, -89]) + (countLit q [-93, -94, -95, -96]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89]) (l₂ := [-93, -94, -95, -96])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1560)) (countLit q [-86, -88, -89]) (countLit q [-93, -94, -95, -96]) (count1557 q) 3 1 (meaning1548 q) (meaning1553 q) (meaning1560 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1553 = false ∨ valuation q 1560 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1564)) (countLit q [-100]) (countLit q [-102]) (count1564 q) 1 (meaningNeg102 q) (meaning1564 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1564 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (1564)) (countLit q [-100]) (countLit q [-102]) (count1564 q) 1 (meaningNeg100 q) (meaning1564 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1564 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1566)) (countLit q [-103]) (countLit q [-105]) (count1566 q) 1 (meaningNeg105 q) (meaning1566 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1566 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1566)) (countLit q [-103]) (countLit q [-105]) (count1566 q) 1 (meaningNeg103 q) (meaning1566 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1566 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1567 = true := by
  have hs : count1566 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1567)) (countLit q [-103]) (countLit q [-105]) (count1566 q) 1 1 (meaningNeg103 q) (meaningNeg105 q) (meaning1567 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 1567 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_right (literal (valuationOf q) (1566)) (literal (valuationOf q) (1568)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1568 q) 1 (meaning1566 q) (meaning1568 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1568 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_right (literal (valuationOf q) (1567)) (literal (valuationOf q) (1569)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1568 q) 2 (meaning1567 q) (meaning1569 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1569 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_left (literal (valuationOf q) (1564)) (literal (valuationOf q) (1568)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1568 q) 1 (meaning1564 q) (meaning1568 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1568 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1569)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1568 q) 1 1 (meaning1564 q) (meaning1566 q) (meaning1569 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1566 = false ∨ valuation q 1569 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1572 = true := by
  have hs : count1572 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (1572)) (countLit q [-109]) (countLit q [-110]) (count1572 q) 1 (meaningNeg110 q) (meaning1572 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1572 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1572 = true := by
  have hs : count1572 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (1572)) (countLit q [-109]) (countLit q [-110]) (count1572 q) 1 (meaningNeg109 q) (meaning1572 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1572 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1574 = true := by
  have hs : count1574 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_right (literal (valuationOf q) (-112)) (literal (valuationOf q) (1574)) (countLit q [-111]) (countLit q [-112]) (count1574 q) 1 (meaningNeg112 q) (meaning1574 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1574 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1574 = true := by
  have hs : count1574 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1574)) (countLit q [-111]) (countLit q [-112]) (count1574 q) 1 (meaningNeg111 q) (meaning1574 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1574 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 112 = true ∨ valuationOf q 1575 = true := by
  have hs : count1574 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-112)) (literal (valuationOf q) (1575)) (countLit q [-111]) (countLit q [-112]) (count1574 q) 1 1 (meaningNeg111 q) (meaningNeg112 q) (meaning1575 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 112)) = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 1575 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-109, -110]) + (countLit q [-111, -112]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-111, -112])
  have hm := merge_right (literal (valuationOf q) (1574)) (literal (valuationOf q) (1576)) (countLit q [-109, -110]) (countLit q [-111, -112]) (count1576 q) 1 (meaning1574 q) (meaning1576 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1576 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1577 = true := by
  have hs : count1576 q = (countLit q [-109, -110]) + (countLit q [-111, -112]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-111, -112])
  have hm := merge_right (literal (valuationOf q) (1575)) (literal (valuationOf q) (1577)) (countLit q [-109, -110]) (countLit q [-111, -112]) (count1576 q) 2 (meaning1575 q) (meaning1577 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1577 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-109, -110]) + (countLit q [-111, -112]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-111, -112])
  have hm := merge_left (literal (valuationOf q) (1572)) (literal (valuationOf q) (1576)) (countLit q [-109, -110]) (countLit q [-111, -112]) (count1576 q) 1 (meaning1572 q) (meaning1576 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1576 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1577 = true := by
  have hs : count1576 q = (countLit q [-109, -110]) + (countLit q [-111, -112]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-111, -112])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1577)) (countLit q [-109, -110]) (countLit q [-111, -112]) (count1576 q) 1 1 (meaning1572 q) (meaning1574 q) (meaning1577 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1574 = false ∨ valuation q 1577 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-100, -102, -103, -105]) + (countLit q [-109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-100, -102, -103, -105]) (l₂ := [-109, -110, -111, -112])
  have hm := merge_right (literal (valuationOf q) (1576)) (literal (valuationOf q) (1580)) (countLit q [-100, -102, -103, -105]) (countLit q [-109, -110, -111, -112]) (count1580 q) 1 (meaning1576 q) (meaning1580 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1580 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-100, -102, -103, -105]) + (countLit q [-109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-100, -102, -103, -105]) (l₂ := [-109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1581)) (countLit q [-100, -102, -103, -105]) (countLit q [-109, -110, -111, -112]) (count1580 q) 1 1 (meaning1568 q) (meaning1576 q) (meaning1581 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1576 = false ∨ valuation q 1581 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1582 = true := by
  have hs : count1580 q = (countLit q [-100, -102, -103, -105]) + (countLit q [-109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-100, -102, -103, -105]) (l₂ := [-109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1582)) (countLit q [-100, -102, -103, -105]) (countLit q [-109, -110, -111, -112]) (count1580 q) 1 2 (meaning1568 q) (meaning1577 q) (meaning1582 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1577 = false ∨ valuation q 1582 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1582 = true := by
  have hs : count1580 q = (countLit q [-100, -102, -103, -105]) + (countLit q [-109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-100, -102, -103, -105]) (l₂ := [-109, -110, -111, -112])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1582)) (countLit q [-100, -102, -103, -105]) (countLit q [-109, -110, -111, -112]) (count1580 q) 2 1 (meaning1569 q) (meaning1576 q) (meaning1582 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1576 = false ∨ valuation q 1582 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1590 = true := by
  have hs : count1588 q = (countLit q [-86, -88, -89, -93, -94, -95, -96]) + (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -89, -93, -94, -95, -96]) (l₂ := [-100, -102, -103, -105, -109, -110, -111, -112])
  have hm := merge_right (literal (valuationOf q) (1582)) (literal (valuationOf q) (1590)) (countLit q [-86, -88, -89, -93, -94, -95, -96]) (countLit q [-100, -102, -103, -105, -109, -110, -111, -112]) (count1588 q) 3 (meaning1582 q) (meaning1590 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1590 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E171.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112171
