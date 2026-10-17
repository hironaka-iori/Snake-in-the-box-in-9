import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1527)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 2 1 (meaning1499 q) (meaning1518 q) (meaning1527 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1518 = false ∨ valuation q 1527 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1528 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1528)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 2 2 (meaning1499 q) (meaning1519 q) (meaning1528 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1519 = false ∨ valuation q 1528 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1529 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1529)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 2 3 (meaning1499 q) (meaning1520 q) (meaning1529 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1520 = false ∨ valuation q 1529 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1500)) (literal (valuationOf q) (1527)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 3 (meaning1500 q) (meaning1527 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1527 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1528 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1528)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 3 1 (meaning1500 q) (meaning1518 q) (meaning1528 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1518 = false ∨ valuation q 1528 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1529 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1529)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 3 2 (meaning1500 q) (meaning1519 q) (meaning1529 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1519 = false ∨ valuation q 1529 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1530 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1530)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 3 3 (meaning1500 q) (meaning1520 q) (meaning1530 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1520 = false ∨ valuation q 1530 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1529 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1529)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 4 1 (meaning1501 q) (meaning1518 q) (meaning1529 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1518 = false ∨ valuation q 1529 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1530 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1530)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 4 2 (meaning1501 q) (meaning1519 q) (meaning1530 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1519 = false ∨ valuation q 1530 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1540 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1540)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 1 2 (meaning1472 q) (meaning1526 q) (meaning1540 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1526 = false ∨ valuation q 1540 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1541 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1541)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 1 3 (meaning1472 q) (meaning1527 q) (meaning1541 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1527 = false ∨ valuation q 1541 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1543 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1543)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 1 5 (meaning1472 q) (meaning1529 q) (meaning1543 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1529 = false ∨ valuation q 1543 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1544 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1544)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 1 6 (meaning1472 q) (meaning1530 q) (meaning1544 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1530 = false ∨ valuation q 1544 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1541 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1541)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 2 2 (meaning1473 q) (meaning1526 q) (meaning1541 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1526 = false ∨ valuation q 1541 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1542 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1542)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 2 3 (meaning1473 q) (meaning1527 q) (meaning1542 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1527 = false ∨ valuation q 1542 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1543 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1543)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 2 4 (meaning1473 q) (meaning1528 q) (meaning1543 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1528 = false ∨ valuation q 1543 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1544 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1544)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 2 5 (meaning1473 q) (meaning1529 q) (meaning1544 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1529 = false ∨ valuation q 1544 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1545 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1545)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 2 6 (meaning1473 q) (meaning1530 q) (meaning1545 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1530 = false ∨ valuation q 1545 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1542 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1542)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 3 2 (meaning1474 q) (meaning1526 q) (meaning1542 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1526 = false ∨ valuation q 1542 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1543 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1543)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 3 3 (meaning1474 q) (meaning1527 q) (meaning1543 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1527 = false ∨ valuation q 1543 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1544 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1544)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 3 4 (meaning1474 q) (meaning1528 q) (meaning1544 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1528 = false ∨ valuation q 1544 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1545 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1545)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 3 5 (meaning1474 q) (meaning1529 q) (meaning1545 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1529 = false ∨ valuation q 1545 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1546 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1546)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 3 6 (meaning1474 q) (meaning1530 q) (meaning1546 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1530 = false ∨ valuation q 1546 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1543 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1543)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 4 2 (meaning1475 q) (meaning1526 q) (meaning1543 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1526 = false ∨ valuation q 1543 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1544 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1544)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 4 3 (meaning1475 q) (meaning1527 q) (meaning1544 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1527 = false ∨ valuation q 1544 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1545 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1545)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 4 4 (meaning1475 q) (meaning1528 q) (meaning1545 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1528 = false ∨ valuation q 1545 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1546 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1546)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 4 5 (meaning1475 q) (meaning1529 q) (meaning1546 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1529 = false ∨ valuation q 1546 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1544 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1476)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1544)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 5 2 (meaning1476 q) (meaning1526 q) (meaning1544 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1526 = false ∨ valuation q 1544 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1545 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1476)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1545)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 5 3 (meaning1476 q) (meaning1527 q) (meaning1545 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1527 = false ∨ valuation q 1545 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1546 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1476)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1546)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 5 4 (meaning1476 q) (meaning1528 q) (meaning1546 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1528 = false ∨ valuation q 1546 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1546 = true := by
  have hs : count1538 q = (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) + (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (l₂ := [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1546)) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]) (countLit q [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1538 q) 6 3 (meaning1477 q) (meaning1527 q) (meaning1546 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1527 = false ∨ valuation q 1546 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1563 = true := by
  have hs : count1551 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) + (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (l₂ := [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1563)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (countLit q [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]) (count1551 q) 4 9 (meaning1426 q) (meaning1546 q) (meaning1563 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1546 = false ∨ valuation q 1563 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E107.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112107
