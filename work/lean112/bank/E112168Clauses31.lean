import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_left (literal (valuationOf q) (1512)) (literal (valuationOf q) (1539)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 3 (meaning1512 q) (meaning1539 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1539 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1540)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 3 1 (meaning1512 q) (meaning1530 q) (meaning1540 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1530 = false ∨ valuation q 1540 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1541)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 3 2 (meaning1512 q) (meaning1531 q) (meaning1541 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1531 = false ∨ valuation q 1541 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1542)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 3 3 (meaning1512 q) (meaning1532 q) (meaning1542 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1532 = false ∨ valuation q 1542 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_left (literal (valuationOf q) (1513)) (literal (valuationOf q) (1540)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 4 (meaning1513 q) (meaning1540 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1540 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1541)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 4 1 (meaning1513 q) (meaning1530 q) (meaning1541 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1530 = false ∨ valuation q 1541 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1542)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 4 2 (meaning1513 q) (meaning1531 q) (meaning1542 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1531 = false ∨ valuation q 1542 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1543 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1543)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 4 3 (meaning1513 q) (meaning1532 q) (meaning1543 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1532 = false ∨ valuation q 1543 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1542)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 5 1 (meaning1514 q) (meaning1530 q) (meaning1542 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1530 = false ∨ valuation q 1542 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1543 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1543)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 5 2 (meaning1514 q) (meaning1531 q) (meaning1543 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1531 = false ∨ valuation q 1543 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1544 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1544)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 5 3 (meaning1514 q) (meaning1532 q) (meaning1544 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1532 = false ∨ valuation q 1544 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1543 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1543)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 6 1 (meaning1515 q) (meaning1530 q) (meaning1543 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1530 = false ∨ valuation q 1543 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1544 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1544)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 6 2 (meaning1515 q) (meaning1531 q) (meaning1544 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1531 = false ∨ valuation q 1544 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1545 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1545)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 6 3 (meaning1515 q) (meaning1532 q) (meaning1545 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1532 = false ∨ valuation q 1545 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-91]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92])
  have hm := merge_right (literal (valuationOf q) (-92)) (literal (valuationOf q) (1551)) (countLit q [-91]) (countLit q [-92]) (count1551 q) 1 (meaningNeg92 q) (meaning1551 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1551 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-91]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1551)) (countLit q [-91]) (countLit q [-92]) (count1551 q) 1 (meaningNeg91 q) (meaning1551 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1551 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 92 = true ∨ valuationOf q 1552 = true := by
  have hs : count1551 q = (countLit q [-91]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-92)) (literal (valuationOf q) (1552)) (countLit q [-91]) (countLit q [-92]) (count1551 q) 1 1 (meaningNeg91 q) (meaningNeg92 q) (meaning1552 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 92)) = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 92 = true ∨ valuation q 1552 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-87]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-91, -92])
  have hm := merge_right (literal (valuationOf q) (1551)) (literal (valuationOf q) (1553)) (countLit q [-87]) (countLit q [-91, -92]) (count1553 q) 1 (meaning1551 q) (meaning1553 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1553 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-87]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-91, -92])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1553)) (countLit q [-87]) (countLit q [-91, -92]) (count1553 q) 1 (meaningNeg87 q) (meaning1553 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1553 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-87]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-91, -92])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1554)) (countLit q [-87]) (countLit q [-91, -92]) (count1553 q) 1 1 (meaningNeg87 q) (meaning1551 q) (meaning1554 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1551 = false ∨ valuation q 1554 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1552 = false ∨ valuationOf q 1555 = true := by
  have hs : count1553 q = (countLit q [-87]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-91, -92])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1555)) (countLit q [-87]) (countLit q [-91, -92]) (count1553 q) 1 2 (meaningNeg87 q) (meaning1552 q) (meaning1555 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1552 = false ∨ valuation q 1555 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1556)) (countLit q [-93]) (countLit q [-94]) (count1556 q) 1 (meaningNeg94 q) (meaning1556 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1556 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1556)) (countLit q [-93]) (countLit q [-94]) (count1556 q) 1 (meaningNeg93 q) (meaning1556 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1556 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 94 = true ∨ valuationOf q 1557 = true := by
  have hs : count1556 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (1557)) (countLit q [-93]) (countLit q [-94]) (count1556 q) 1 1 (meaningNeg93 q) (meaningNeg94 q) (meaning1557 q) hs
  change (! (valuationOf q 93)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 94 = true ∨ valuation q 1557 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1558)) (countLit q [-98]) (countLit q [-100]) (count1558 q) 1 (meaningNeg100 q) (meaning1558 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1558 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1558)) (countLit q [-98]) (countLit q [-100]) (count1558 q) 1 (meaningNeg98 q) (meaning1558 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1558 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1559 = true := by
  have hs : count1558 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1559)) (countLit q [-98]) (countLit q [-100]) (count1558 q) 1 1 (meaningNeg98 q) (meaningNeg100 q) (meaning1559 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 100 = true ∨ valuation q 1559 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-93, -94]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-98, -100])
  have hm := merge_right (literal (valuationOf q) (1558)) (literal (valuationOf q) (1560)) (countLit q [-93, -94]) (countLit q [-98, -100]) (count1560 q) 1 (meaning1558 q) (meaning1560 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1560 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-93, -94]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-98, -100])
  have hm := merge_right (literal (valuationOf q) (1559)) (literal (valuationOf q) (1561)) (countLit q [-93, -94]) (countLit q [-98, -100]) (count1560 q) 2 (meaning1559 q) (meaning1561 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1561 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-93, -94]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-98, -100])
  have hm := merge_left (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-93, -94]) (countLit q [-98, -100]) (count1560 q) 1 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-93, -94]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1561)) (countLit q [-93, -94]) (countLit q [-98, -100]) (count1560 q) 1 1 (meaning1556 q) (meaning1558 q) (meaning1561 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = false ∨ valuation q 1561 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true := by
  have hs : count1560 q = (countLit q [-93, -94]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1562)) (countLit q [-93, -94]) (countLit q [-98, -100]) (count1560 q) 1 2 (meaning1556 q) (meaning1559 q) (meaning1562 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1559 = false ∨ valuation q 1562 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E168.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112168
