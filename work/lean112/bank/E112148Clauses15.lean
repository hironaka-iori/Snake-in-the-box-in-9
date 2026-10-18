import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1500)) (countLit q [-85]) (countLit q [-86]) (count1499 q) 1 1 (meaningNeg85 q) (meaningNeg86 q) (meaning1500 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 1500 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-82]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1499)) (literal (valuationOf q) (1501)) (countLit q [-82]) (countLit q [-85, -86]) (count1501 q) 1 (meaning1499 q) (meaning1501 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1501 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-82]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85, -86])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1501)) (countLit q [-82]) (countLit q [-85, -86]) (count1501 q) 1 (meaningNeg82 q) (meaning1501 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1501 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1499 = false ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-82]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1502)) (countLit q [-82]) (countLit q [-85, -86]) (count1501 q) 1 1 (meaningNeg82 q) (meaning1499 q) (meaning1502 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1499 = false ∨ valuation q 1502 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1500 = false ∨ valuationOf q 1503 = true := by
  have hs : count1501 q = (countLit q [-82]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1503)) (countLit q [-82]) (countLit q [-85, -86]) (count1501 q) 1 2 (meaningNeg82 q) (meaning1500 q) (meaning1503 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1500 = false ∨ valuation q 1503 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-88]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1504)) (countLit q [-88]) (countLit q [-93]) (count1504 q) 1 (meaningNeg93 q) (meaning1504 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1504 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-88]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1504)) (countLit q [-88]) (countLit q [-93]) (count1504 q) 1 (meaningNeg88 q) (meaning1504 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1504 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-88]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1505)) (countLit q [-88]) (countLit q [-93]) (count1504 q) 1 1 (meaningNeg88 q) (meaningNeg93 q) (meaning1505 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 93 = true ∨ valuation q 1505 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-94]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1506)) (countLit q [-94]) (countLit q [-97]) (count1506 q) 1 (meaningNeg97 q) (meaning1506 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1506 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-94]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1506)) (countLit q [-94]) (countLit q [-97]) (count1506 q) 1 (meaningNeg94 q) (meaning1506 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1506 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-94]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1507)) (countLit q [-94]) (countLit q [-97]) (count1506 q) 1 1 (meaningNeg94 q) (meaningNeg97 q) (meaning1507 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 97 = true ∨ valuation q 1507 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-88, -93]) + (countLit q [-94, -97]) := List.countP_append (p := literal q) (l₁ := [-88, -93]) (l₂ := [-94, -97])
  have hm := merge_right (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (countLit q [-88, -93]) (countLit q [-94, -97]) (count1508 q) 1 (meaning1506 q) (meaning1508 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-88, -93]) + (countLit q [-94, -97]) := List.countP_append (p := literal q) (l₁ := [-88, -93]) (l₂ := [-94, -97])
  have hm := merge_right (literal (valuationOf q) (1507)) (literal (valuationOf q) (1509)) (countLit q [-88, -93]) (countLit q [-94, -97]) (count1508 q) 2 (meaning1507 q) (meaning1509 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1509 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-88, -93]) + (countLit q [-94, -97]) := List.countP_append (p := literal q) (l₁ := [-88, -93]) (l₂ := [-94, -97])
  have hm := merge_left (literal (valuationOf q) (1504)) (literal (valuationOf q) (1508)) (countLit q [-88, -93]) (countLit q [-94, -97]) (count1508 q) 1 (meaning1504 q) (meaning1508 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1508 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-88, -93]) + (countLit q [-94, -97]) := List.countP_append (p := literal q) (l₁ := [-88, -93]) (l₂ := [-94, -97])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1509)) (countLit q [-88, -93]) (countLit q [-94, -97]) (count1508 q) 1 1 (meaning1504 q) (meaning1506 q) (meaning1509 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1506 = false ∨ valuation q 1509 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-88, -93]) + (countLit q [-94, -97]) := List.countP_append (p := literal q) (l₁ := [-88, -93]) (l₂ := [-94, -97])
  have hm := merge_left (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-88, -93]) (countLit q [-94, -97]) (count1508 q) 2 (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1509 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-88, -93]) + (countLit q [-94, -97]) := List.countP_append (p := literal q) (l₁ := [-88, -93]) (l₂ := [-94, -97])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-88, -93]) (countLit q [-94, -97]) (count1508 q) 2 1 (meaning1505 q) (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1506 = false ∨ valuation q 1510 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-82, -85, -86]) + (countLit q [-88, -93, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86]) (l₂ := [-88, -93, -94, -97])
  have hm := merge_left (literal (valuationOf q) (1501)) (literal (valuationOf q) (1512)) (countLit q [-82, -85, -86]) (countLit q [-88, -93, -94, -97]) (count1512 q) 1 (meaning1501 q) (meaning1512 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1512 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-82, -85, -86]) + (countLit q [-88, -93, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86]) (l₂ := [-88, -93, -94, -97])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1513)) (countLit q [-82, -85, -86]) (countLit q [-88, -93, -94, -97]) (count1512 q) 1 1 (meaning1501 q) (meaning1508 q) (meaning1513 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1508 = false ∨ valuation q 1513 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true := by
  have hs : count1512 q = (countLit q [-82, -85, -86]) + (countLit q [-88, -93, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86]) (l₂ := [-88, -93, -94, -97])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1514)) (countLit q [-82, -85, -86]) (countLit q [-88, -93, -94, -97]) (count1512 q) 1 2 (meaning1501 q) (meaning1509 q) (meaning1514 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1509 = false ∨ valuation q 1514 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true := by
  have hs : count1512 q = (countLit q [-82, -85, -86]) + (countLit q [-88, -93, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86]) (l₂ := [-88, -93, -94, -97])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1515)) (countLit q [-82, -85, -86]) (countLit q [-88, -93, -94, -97]) (count1512 q) 1 3 (meaning1501 q) (meaning1510 q) (meaning1515 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1510 = false ∨ valuation q 1515 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true := by
  have hs : count1512 q = (countLit q [-82, -85, -86]) + (countLit q [-88, -93, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86]) (l₂ := [-88, -93, -94, -97])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (countLit q [-82, -85, -86]) (countLit q [-88, -93, -94, -97]) (count1512 q) 2 1 (meaning1502 q) (meaning1508 q) (meaning1514 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1508 = false ∨ valuation q 1514 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1515 = true := by
  have hs : count1512 q = (countLit q [-82, -85, -86]) + (countLit q [-88, -93, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86]) (l₂ := [-88, -93, -94, -97])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1515)) (countLit q [-82, -85, -86]) (countLit q [-88, -93, -94, -97]) (count1512 q) 2 2 (meaning1502 q) (meaning1509 q) (meaning1515 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1509 = false ∨ valuation q 1515 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1514 = true := by
  have hs : count1512 q = (countLit q [-82, -85, -86]) + (countLit q [-88, -93, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86]) (l₂ := [-88, -93, -94, -97])
  have hm := merge_left (literal (valuationOf q) (1503)) (literal (valuationOf q) (1514)) (countLit q [-82, -85, -86]) (countLit q [-88, -93, -94, -97]) (count1512 q) 3 (meaning1503 q) (meaning1514 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1514 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1515 = true := by
  have hs : count1512 q = (countLit q [-82, -85, -86]) + (countLit q [-88, -93, -94, -97]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86]) (l₂ := [-88, -93, -94, -97])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1515)) (countLit q [-82, -85, -86]) (countLit q [-88, -93, -94, -97]) (count1512 q) 3 1 (meaning1503 q) (meaning1508 q) (meaning1515 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1508 = false ∨ valuation q 1515 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-100]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-103])
  have hm := merge_right (literal (valuationOf q) (-103)) (literal (valuationOf q) (1519)) (countLit q [-100]) (countLit q [-103]) (count1519 q) 1 (meaningNeg103 q) (meaning1519 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1519 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-99]) + (countLit q [-100, -103]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100, -103])
  have hm := merge_right (literal (valuationOf q) (1519)) (literal (valuationOf q) (1521)) (countLit q [-99]) (countLit q [-100, -103]) (count1521 q) 1 (meaning1519 q) (meaning1521 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1521 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-99]) + (countLit q [-100, -103]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100, -103])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1521)) (countLit q [-99]) (countLit q [-100, -103]) (count1521 q) 1 (meaningNeg99 q) (meaning1521 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1521 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-105]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1524)) (countLit q [-105]) (countLit q [-106]) (count1524 q) 1 (meaningNeg106 q) (meaning1524 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1524 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-105, -106]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-108, -109])
  have hm := merge_left (literal (valuationOf q) (1524)) (literal (valuationOf q) (1528)) (countLit q [-105, -106]) (countLit q [-108, -109]) (count1528 q) 1 (meaning1524 q) (meaning1528 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1528 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1532 = true := by
  have hs : count1532 q = (countLit q [-99, -100, -103]) + (countLit q [-105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -103]) (l₂ := [-105, -106, -108, -109])
  have hm := merge_right (literal (valuationOf q) (1528)) (literal (valuationOf q) (1532)) (countLit q [-99, -100, -103]) (countLit q [-105, -106, -108, -109]) (count1532 q) 1 (meaning1528 q) (meaning1532 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1532 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1532 = true := by
  have hs : count1532 q = (countLit q [-99, -100, -103]) + (countLit q [-105, -106, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -103]) (l₂ := [-105, -106, -108, -109])
  have hm := merge_left (literal (valuationOf q) (1521)) (literal (valuationOf q) (1532)) (countLit q [-99, -100, -103]) (countLit q [-105, -106, -108, -109]) (count1532 q) 1 (meaning1521 q) (meaning1532 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1532 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E148.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112148
