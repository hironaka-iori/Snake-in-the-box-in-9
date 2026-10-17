import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1518 = true := by
  have hs : count1517 q = (countLit q [-72, -74, -76, -77]) + (countLit q [-80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -77]) (l₂ := [-80, -81, -83, -84])
  have hm := merge_right (literal (valuationOf q) (1514)) (literal (valuationOf q) (1518)) (countLit q [-72, -74, -76, -77]) (countLit q [-80, -81, -83, -84]) (count1517 q) 2 (meaning1514 q) (meaning1518 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1518 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-72, -74, -76, -77]) + (countLit q [-80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -77]) (l₂ := [-80, -81, -83, -84])
  have hm := merge_left (literal (valuationOf q) (1505)) (literal (valuationOf q) (1517)) (countLit q [-72, -74, -76, -77]) (countLit q [-80, -81, -83, -84]) (count1517 q) 1 (meaning1505 q) (meaning1517 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1517 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1518 = true := by
  have hs : count1517 q = (countLit q [-72, -74, -76, -77]) + (countLit q [-80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -77]) (l₂ := [-80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1518)) (countLit q [-72, -74, -76, -77]) (countLit q [-80, -81, -83, -84]) (count1517 q) 1 1 (meaning1505 q) (meaning1513 q) (meaning1518 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1513 = false ∨ valuation q 1518 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true := by
  have hs : count1517 q = (countLit q [-72, -74, -76, -77]) + (countLit q [-80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -77]) (l₂ := [-80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1519)) (countLit q [-72, -74, -76, -77]) (countLit q [-80, -81, -83, -84]) (count1517 q) 1 2 (meaning1505 q) (meaning1514 q) (meaning1519 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1514 = false ∨ valuation q 1519 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1518 = true := by
  have hs : count1517 q = (countLit q [-72, -74, -76, -77]) + (countLit q [-80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -77]) (l₂ := [-80, -81, -83, -84])
  have hm := merge_left (literal (valuationOf q) (1506)) (literal (valuationOf q) (1518)) (countLit q [-72, -74, -76, -77]) (countLit q [-80, -81, -83, -84]) (count1517 q) 2 (meaning1506 q) (meaning1518 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1518 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1519 = true := by
  have hs : count1517 q = (countLit q [-72, -74, -76, -77]) + (countLit q [-80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -77]) (l₂ := [-80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1519)) (countLit q [-72, -74, -76, -77]) (countLit q [-80, -81, -83, -84]) (count1517 q) 2 1 (meaning1506 q) (meaning1513 q) (meaning1519 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1513 = false ∨ valuation q 1519 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1519 = true := by
  have hs : count1517 q = (countLit q [-72, -74, -76, -77]) + (countLit q [-80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -77]) (l₂ := [-80, -81, -83, -84])
  have hm := merge_left (literal (valuationOf q) (1507)) (literal (valuationOf q) (1519)) (countLit q [-72, -74, -76, -77]) (countLit q [-80, -81, -83, -84]) (count1517 q) 3 (meaning1507 q) (meaning1519 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1519 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1520 = true := by
  have hs : count1517 q = (countLit q [-72, -74, -76, -77]) + (countLit q [-80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -77]) (l₂ := [-80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1520)) (countLit q [-72, -74, -76, -77]) (countLit q [-80, -81, -83, -84]) (count1517 q) 3 1 (meaning1507 q) (meaning1513 q) (meaning1520 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1513 = false ∨ valuation q 1520 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1525 = true := by
  have hs : count1525 q = (countLit q [-56, -59, -60, -64, -65, -67, -69]) + (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69]) (l₂ := [-72, -74, -76, -77, -80, -81, -83, -84])
  have hm := merge_right (literal (valuationOf q) (1517)) (literal (valuationOf q) (1525)) (countLit q [-56, -59, -60, -64, -65, -67, -69]) (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) (count1525 q) 1 (meaning1517 q) (meaning1525 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1525 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-56, -59, -60, -64, -65, -67, -69]) + (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69]) (l₂ := [-72, -74, -76, -77, -80, -81, -83, -84])
  have hm := merge_right (literal (valuationOf q) (1518)) (literal (valuationOf q) (1526)) (countLit q [-56, -59, -60, -64, -65, -67, -69]) (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) (count1525 q) 2 (meaning1518 q) (meaning1526 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1526 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-56, -59, -60, -64, -65, -67, -69]) + (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69]) (l₂ := [-72, -74, -76, -77, -80, -81, -83, -84])
  have hm := merge_right (literal (valuationOf q) (1519)) (literal (valuationOf q) (1527)) (countLit q [-56, -59, -60, -64, -65, -67, -69]) (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) (count1525 q) 3 (meaning1519 q) (meaning1527 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1527 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-56, -59, -60, -64, -65, -67, -69]) + (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69]) (l₂ := [-72, -74, -76, -77, -80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1526)) (countLit q [-56, -59, -60, -64, -65, -67, -69]) (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) (count1525 q) 1 1 (meaning1494 q) (meaning1517 q) (meaning1526 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1517 = false ∨ valuation q 1526 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-56, -59, -60, -64, -65, -67, -69]) + (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69]) (l₂ := [-72, -74, -76, -77, -80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1527)) (countLit q [-56, -59, -60, -64, -65, -67, -69]) (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) (count1525 q) 1 2 (meaning1494 q) (meaning1518 q) (meaning1527 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1518 = false ∨ valuation q 1527 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1528 = true := by
  have hs : count1525 q = (countLit q [-56, -59, -60, -64, -65, -67, -69]) + (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69]) (l₂ := [-72, -74, -76, -77, -80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1528)) (countLit q [-56, -59, -60, -64, -65, -67, -69]) (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) (count1525 q) 1 3 (meaning1494 q) (meaning1519 q) (meaning1528 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1519 = false ∨ valuation q 1528 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1529 = true := by
  have hs : count1525 q = (countLit q [-56, -59, -60, -64, -65, -67, -69]) + (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69]) (l₂ := [-72, -74, -76, -77, -80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1529)) (countLit q [-56, -59, -60, -64, -65, -67, -69]) (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) (count1525 q) 1 4 (meaning1494 q) (meaning1520 q) (meaning1529 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1520 = false ∨ valuation q 1529 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-56, -59, -60, -64, -65, -67, -69]) + (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69]) (l₂ := [-72, -74, -76, -77, -80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1527)) (countLit q [-56, -59, -60, -64, -65, -67, -69]) (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) (count1525 q) 2 1 (meaning1495 q) (meaning1517 q) (meaning1527 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1517 = false ∨ valuation q 1527 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1528 = true := by
  have hs : count1525 q = (countLit q [-56, -59, -60, -64, -65, -67, -69]) + (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69]) (l₂ := [-72, -74, -76, -77, -80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1528)) (countLit q [-56, -59, -60, -64, -65, -67, -69]) (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) (count1525 q) 2 2 (meaning1495 q) (meaning1518 q) (meaning1528 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1518 = false ∨ valuation q 1528 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1529 = true := by
  have hs : count1525 q = (countLit q [-56, -59, -60, -64, -65, -67, -69]) + (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69]) (l₂ := [-72, -74, -76, -77, -80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1529)) (countLit q [-56, -59, -60, -64, -65, -67, -69]) (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) (count1525 q) 2 3 (meaning1495 q) (meaning1519 q) (meaning1529 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1519 = false ∨ valuation q 1529 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1528 = true := by
  have hs : count1525 q = (countLit q [-56, -59, -60, -64, -65, -67, -69]) + (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69]) (l₂ := [-72, -74, -76, -77, -80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1528)) (countLit q [-56, -59, -60, -64, -65, -67, -69]) (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) (count1525 q) 3 1 (meaning1496 q) (meaning1517 q) (meaning1528 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1517 = false ∨ valuation q 1528 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1529 = true := by
  have hs : count1525 q = (countLit q [-56, -59, -60, -64, -65, -67, -69]) + (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69]) (l₂ := [-72, -74, -76, -77, -80, -81, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1529)) (countLit q [-56, -59, -60, -64, -65, -67, -69]) (countLit q [-72, -74, -76, -77, -80, -81, -83, -84]) (count1525 q) 3 2 (meaning1496 q) (meaning1518 q) (meaning1529 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1518 = false ∨ valuation q 1529 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1540 = true := by
  have hs : count1540 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1540)) (countLit q [-88]) (countLit q [-90]) (count1540 q) 1 (meaningNeg90 q) (meaning1540 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1540 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1540 = true := by
  have hs : count1540 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1540)) (countLit q [-88]) (countLit q [-90]) (count1540 q) 1 (meaningNeg88 q) (meaning1540 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1540 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 90 = true ∨ valuationOf q 1541 = true := by
  have hs : count1540 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (1541)) (countLit q [-88]) (countLit q [-90]) (count1540 q) 1 1 (meaningNeg88 q) (meaningNeg90 q) (meaning1541 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 1541 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1542 = true := by
  have hs : count1542 q = (countLit q [-86]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -90])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1542)) (countLit q [-86]) (countLit q [-88, -90]) (count1542 q) 1 (meaningNeg86 q) (meaning1542 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1542 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1540 = false ∨ valuationOf q 1543 = true := by
  have hs : count1542 q = (countLit q [-86]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -90])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1543)) (countLit q [-86]) (countLit q [-88, -90]) (count1542 q) 1 1 (meaningNeg86 q) (meaning1540 q) (meaning1543 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1540 = false ∨ valuation q 1543 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1541 = false ∨ valuationOf q 1544 = true := by
  have hs : count1542 q = (countLit q [-86]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -90])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1544)) (countLit q [-86]) (countLit q [-88, -90]) (count1542 q) 1 2 (meaningNeg86 q) (meaning1541 q) (meaning1544 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1541 = false ∨ valuation q 1544 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1545 = true := by
  have hs : count1545 q = (countLit q [-91]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1545)) (countLit q [-91]) (countLit q [-94]) (count1545 q) 1 (meaningNeg94 q) (meaning1545 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1545 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1545 = true := by
  have hs : count1545 q = (countLit q [-91]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1545)) (countLit q [-91]) (countLit q [-94]) (count1545 q) 1 (meaningNeg91 q) (meaning1545 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1545 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1547)) (countLit q [-95]) (countLit q [-97]) (count1547 q) 1 (meaningNeg97 q) (meaning1547 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1547 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1548 = true := by
  have hs : count1547 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1548)) (countLit q [-95]) (countLit q [-97]) (count1547 q) 1 1 (meaningNeg95 q) (meaningNeg97 q) (meaning1548 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 1548 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-91, -94]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-91, -94]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuationOf q) (1547)) (literal (valuationOf q) (1549)) (countLit q [-91, -94]) (countLit q [-95, -97]) (count1549 q) 1 (meaning1547 q) (meaning1549 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1549 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1550 = true := by
  have hs : count1549 q = (countLit q [-91, -94]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-91, -94]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuationOf q) (1548)) (literal (valuationOf q) (1550)) (countLit q [-91, -94]) (countLit q [-95, -97]) (count1549 q) 2 (meaning1548 q) (meaning1550 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1550 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E146.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112146
