import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1437)) (countLit q [-100]) (countLit q [-102]) (count1437 q) 1 (meaningNeg102 q) (meaning1437 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1437 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (1437)) (countLit q [-100]) (countLit q [-102]) (count1437 q) 1 (meaningNeg100 q) (meaning1437 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1437 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 102 = true ∨ valuationOf q 1438 = true := by
  have hs : count1437 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_two (literal (valuationOf q) (-100)) (literal (valuationOf q) (-102)) (literal (valuationOf q) (1438)) (countLit q [-100]) (countLit q [-102]) (count1437 q) 1 1 (meaningNeg100 q) (meaningNeg102 q) (meaning1438 q) hs
  change (! (valuationOf q 100)) = false ∨ (! (valuationOf q 102)) = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 102 = true ∨ valuation q 1438 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1439)) (countLit q [-103]) (countLit q [-105]) (count1439 q) 1 (meaningNeg105 q) (meaning1439 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1439 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1439)) (countLit q [-103]) (countLit q [-105]) (count1439 q) 1 (meaningNeg103 q) (meaning1439 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1439 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_right (literal (valuationOf q) (1439)) (literal (valuationOf q) (1441)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1441 q) 1 (meaning1439 q) (meaning1441 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1441 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_left (literal (valuationOf q) (1437)) (literal (valuationOf q) (1441)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1441 q) 1 (meaning1437 q) (meaning1441 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1441 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1442)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1441 q) 1 1 (meaning1437 q) (meaning1439 q) (meaning1442 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1439 = false ∨ valuation q 1442 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1443)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1441 q) 2 1 (meaning1438 q) (meaning1439 q) (meaning1443 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1439 = false ∨ valuation q 1443 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-93, -96, -98]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -98]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1441)) (literal (valuationOf q) (1445)) (countLit q [-93, -96, -98]) (countLit q [-100, -102, -103, -105]) (count1445 q) 1 (meaning1441 q) (meaning1445 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1445 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-93, -96, -98]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -98]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1442)) (literal (valuationOf q) (1446)) (countLit q [-93, -96, -98]) (countLit q [-100, -102, -103, -105]) (count1445 q) 2 (meaning1442 q) (meaning1446 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1446 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1447 = true := by
  have hs : count1445 q = (countLit q [-93, -96, -98]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -98]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1443)) (literal (valuationOf q) (1447)) (countLit q [-93, -96, -98]) (countLit q [-100, -102, -103, -105]) (count1445 q) 3 (meaning1443 q) (meaning1447 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1447 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-93, -96, -98]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -98]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1434)) (literal (valuationOf q) (1445)) (countLit q [-93, -96, -98]) (countLit q [-100, -102, -103, -105]) (count1445 q) 1 (meaning1434 q) (meaning1445 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1445 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-93, -96, -98]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -98]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1446)) (countLit q [-93, -96, -98]) (countLit q [-100, -102, -103, -105]) (count1445 q) 1 1 (meaning1434 q) (meaning1441 q) (meaning1446 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1441 = false ∨ valuation q 1446 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1447 = true := by
  have hs : count1445 q = (countLit q [-93, -96, -98]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -98]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1447)) (countLit q [-93, -96, -98]) (countLit q [-100, -102, -103, -105]) (count1445 q) 1 2 (meaning1434 q) (meaning1442 q) (meaning1447 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1442 = false ∨ valuation q 1447 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1448 = true := by
  have hs : count1445 q = (countLit q [-93, -96, -98]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -98]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1448)) (countLit q [-93, -96, -98]) (countLit q [-100, -102, -103, -105]) (count1445 q) 1 3 (meaning1434 q) (meaning1443 q) (meaning1448 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1443 = false ∨ valuation q 1448 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-93, -96, -98]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -98]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1435)) (literal (valuationOf q) (1446)) (countLit q [-93, -96, -98]) (countLit q [-100, -102, -103, -105]) (count1445 q) 2 (meaning1435 q) (meaning1446 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1446 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1447 = true := by
  have hs : count1445 q = (countLit q [-93, -96, -98]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -98]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1447)) (countLit q [-93, -96, -98]) (countLit q [-100, -102, -103, -105]) (count1445 q) 2 1 (meaning1435 q) (meaning1441 q) (meaning1447 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1441 = false ∨ valuation q 1447 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1448 = true := by
  have hs : count1445 q = (countLit q [-93, -96, -98]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -98]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1448)) (countLit q [-93, -96, -98]) (countLit q [-100, -102, -103, -105]) (count1445 q) 2 2 (meaning1435 q) (meaning1442 q) (meaning1448 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1442 = false ∨ valuation q 1448 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1447 = true := by
  have hs : count1445 q = (countLit q [-93, -96, -98]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -98]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1436)) (literal (valuationOf q) (1447)) (countLit q [-93, -96, -98]) (countLit q [-100, -102, -103, -105]) (count1445 q) 3 (meaning1436 q) (meaning1447 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1447 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1445)) (literal (valuationOf q) (1452)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 1 (meaning1445 q) (meaning1452 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1452 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1453)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 2 (meaning1446 q) (meaning1453 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1453 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1454)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 3 (meaning1447 q) (meaning1454 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1454 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1455)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 4 (meaning1448 q) (meaning1455 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1455 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1425)) (literal (valuationOf q) (1452)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 1 (meaning1425 q) (meaning1452 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1452 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1453)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 1 1 (meaning1425 q) (meaning1445 q) (meaning1453 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1445 = false ∨ valuation q 1453 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1454)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 1 2 (meaning1425 q) (meaning1446 q) (meaning1454 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1446 = false ∨ valuation q 1454 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1455)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 1 3 (meaning1425 q) (meaning1447 q) (meaning1455 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1447 = false ∨ valuation q 1455 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1426)) (literal (valuationOf q) (1453)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 2 (meaning1426 q) (meaning1453 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1453 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1454)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 2 1 (meaning1426 q) (meaning1445 q) (meaning1454 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1445 = false ∨ valuation q 1454 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1455)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 2 2 (meaning1426 q) (meaning1446 q) (meaning1455 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1446 = false ∨ valuation q 1455 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1456 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1456)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 2 3 (meaning1426 q) (meaning1447 q) (meaning1456 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1447 = false ∨ valuation q 1456 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E091.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112091
