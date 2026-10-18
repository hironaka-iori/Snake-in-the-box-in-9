import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 988 = false ∨ valuationOf q 991 = true := by
  have hs : count990 q = (countLit q [-62]) + (countLit q [-63, -65]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -65])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (988)) (literal (valuationOf q) (991)) (countLit q [-62]) (countLit q [-63, -65]) (count990 q) 1 1 (meaningNeg62 q) (meaning988 q) (meaning991 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 988 = false ∨ valuationOf q 991 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 988 = false ∨ valuation q 991 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 989 = false ∨ valuationOf q 992 = true := by
  have hs : count990 q = (countLit q [-62]) + (countLit q [-63, -65]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -65])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (989)) (literal (valuationOf q) (992)) (countLit q [-62]) (countLit q [-63, -65]) (count990 q) 1 2 (meaningNeg62 q) (meaning989 q) (meaning992 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 989 = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 989 = false ∨ valuation q 992 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 993 = true := by
  have hs : count993 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (993)) (countLit q [-67]) (countLit q [-68]) (count993 q) 1 (meaningNeg68 q) (meaning993 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 993 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 993 = true := by
  have hs : count993 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (993)) (countLit q [-67]) (countLit q [-68]) (count993 q) 1 (meaningNeg67 q) (meaning993 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 993 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 68 = true ∨ valuationOf q 994 = true := by
  have hs : count993 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (994)) (countLit q [-67]) (countLit q [-68]) (count993 q) 1 1 (meaningNeg67 q) (meaningNeg68 q) (meaning994 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 68 = true ∨ valuation q 994 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 995 = true := by
  have hs : count995 q = (countLit q [-70]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (995)) (countLit q [-70]) (countLit q [-74]) (count995 q) 1 (meaningNeg74 q) (meaning995 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 995 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 995 = true := by
  have hs : count995 q = (countLit q [-70]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (995)) (countLit q [-70]) (countLit q [-74]) (count995 q) 1 (meaningNeg70 q) (meaning995 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 995 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 74 = true ∨ valuationOf q 996 = true := by
  have hs : count995 q = (countLit q [-70]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (996)) (countLit q [-70]) (countLit q [-74]) (count995 q) 1 1 (meaningNeg70 q) (meaningNeg74 q) (meaning996 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 996 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 996 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 995 = false ∨ valuationOf q 997 = true := by
  have hs : count997 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_right (literal (valuationOf q) (995)) (literal (valuationOf q) (997)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count997 q) 1 (meaning995 q) (meaning997 q) hs
  change valuationOf q 995 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 995 = false ∨ valuation q 997 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_right (literal (valuationOf q) (996)) (literal (valuationOf q) (998)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count997 q) 2 (meaning996 q) (meaning998 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 998 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 997 = true := by
  have hs : count997 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_left (literal (valuationOf q) (993)) (literal (valuationOf q) (997)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count997 q) 1 (meaning993 q) (meaning997 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 997 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 995 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (995)) (literal (valuationOf q) (998)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count997 q) 1 1 (meaning993 q) (meaning995 q) (meaning998 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 995 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 995 = false ∨ valuation q 998 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 996 = false ∨ valuationOf q 999 = true := by
  have hs : count997 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (996)) (literal (valuationOf q) (999)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count997 q) 1 2 (meaning993 q) (meaning996 q) (meaning999 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 996 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 996 = false ∨ valuation q 999 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_left (literal (valuationOf q) (994)) (literal (valuationOf q) (998)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count997 q) 2 (meaning994 q) (meaning998 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 998 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 995 = false ∨ valuationOf q 999 = true := by
  have hs : count997 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (995)) (literal (valuationOf q) (999)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count997 q) 2 1 (meaning994 q) (meaning995 q) (meaning999 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 995 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 995 = false ∨ valuation q 999 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1000 = true := by
  have hs : count997 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (996)) (literal (valuationOf q) (1000)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count997 q) 2 2 (meaning994 q) (meaning996 q) (meaning1000 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 996 = false ∨ valuation q 1000 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_right (literal (valuationOf q) (997)) (literal (valuationOf q) (1001)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 1 (meaning997 q) (meaning1001 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1001 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_right (literal (valuationOf q) (998)) (literal (valuationOf q) (1002)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 2 (meaning998 q) (meaning1002 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 1002 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_right (literal (valuationOf q) (999)) (literal (valuationOf q) (1003)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 3 (meaning999 q) (meaning1003 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1003 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_right (literal (valuationOf q) (1000)) (literal (valuationOf q) (1004)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 4 (meaning1000 q) (meaning1004 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1004 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_left (literal (valuationOf q) (990)) (literal (valuationOf q) (1001)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 1 (meaning990 q) (meaning1001 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 1001 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1002)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 1 1 (meaning990 q) (meaning997 q) (meaning1002 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 997 = false ∨ valuation q 1002 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1003)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 1 2 (meaning990 q) (meaning998 q) (meaning1003 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 998 = false ∨ valuation q 1003 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1004)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 1 3 (meaning990 q) (meaning999 q) (meaning1004 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 999 = false ∨ valuation q 1004 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1005 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (1000)) (literal (valuationOf q) (1005)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 1 4 (meaning990 q) (meaning1000 q) (meaning1005 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 1000 = false ∨ valuation q 1005 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_left (literal (valuationOf q) (991)) (literal (valuationOf q) (1002)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 2 (meaning991 q) (meaning1002 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 1002 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1003)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 2 1 (meaning991 q) (meaning997 q) (meaning1003 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 997 = false ∨ valuation q 1003 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1004)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 2 2 (meaning991 q) (meaning998 q) (meaning1004 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 998 = false ∨ valuation q 1004 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1005 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1005)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 2 3 (meaning991 q) (meaning999 q) (meaning1005 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 999 = false ∨ valuation q 1005 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1006 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (1000)) (literal (valuationOf q) (1006)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 2 4 (meaning991 q) (meaning1000 q) (meaning1006 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 1000 = false ∨ valuation q 1006 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_left (literal (valuationOf q) (992)) (literal (valuationOf q) (1003)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 3 (meaning992 q) (meaning1003 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 1003 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-62, -63, -65]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1004)) (countLit q [-62, -63, -65]) (countLit q [-67, -68, -70, -74]) (count1001 q) 3 1 (meaning992 q) (meaning997 q) (meaning1004 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 997 = false ∨ valuation q 1004 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E256.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112256
