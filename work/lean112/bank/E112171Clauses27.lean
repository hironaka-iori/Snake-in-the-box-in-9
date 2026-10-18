import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 71 = true ∨ valuationOf q 1498 = true := by
  have hs : count1497 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-71)) (literal (valuationOf q) (1498)) (countLit q [-69]) (countLit q [-71]) (count1497 q) 1 1 (meaningNeg69 q) (meaningNeg71 q) (meaning1498 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 71)) = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 71 = true ∨ valuation q 1498 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-66, -68]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -71])
  have hm := merge_right (literal (valuationOf q) (1497)) (literal (valuationOf q) (1499)) (countLit q [-66, -68]) (countLit q [-69, -71]) (count1499 q) 1 (meaning1497 q) (meaning1499 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1499 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-66, -68]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -71])
  have hm := merge_right (literal (valuationOf q) (1498)) (literal (valuationOf q) (1500)) (countLit q [-66, -68]) (countLit q [-69, -71]) (count1499 q) 2 (meaning1498 q) (meaning1500 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1500 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-66, -68]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -71])
  have hm := merge_left (literal (valuationOf q) (1495)) (literal (valuationOf q) (1499)) (countLit q [-66, -68]) (countLit q [-69, -71]) (count1499 q) 1 (meaning1495 q) (meaning1499 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1499 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-66, -68]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -71])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1500)) (countLit q [-66, -68]) (countLit q [-69, -71]) (count1499 q) 1 1 (meaning1495 q) (meaning1497 q) (meaning1500 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1497 = false ∨ valuation q 1500 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1501 = true := by
  have hs : count1499 q = (countLit q [-66, -68]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -71])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1501)) (countLit q [-66, -68]) (countLit q [-69, -71]) (count1499 q) 1 2 (meaning1495 q) (meaning1498 q) (meaning1501 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1498 = false ∨ valuation q 1501 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-66, -68]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -71])
  have hm := merge_left (literal (valuationOf q) (1496)) (literal (valuationOf q) (1500)) (countLit q [-66, -68]) (countLit q [-69, -71]) (count1499 q) 2 (meaning1496 q) (meaning1500 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1500 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1501 = true := by
  have hs : count1499 q = (countLit q [-66, -68]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -71])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1501)) (countLit q [-66, -68]) (countLit q [-69, -71]) (count1499 q) 2 1 (meaning1496 q) (meaning1497 q) (meaning1501 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1497 = false ∨ valuation q 1501 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1502 = true := by
  have hs : count1499 q = (countLit q [-66, -68]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -71])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1502)) (countLit q [-66, -68]) (countLit q [-69, -71]) (count1499 q) 2 2 (meaning1496 q) (meaning1498 q) (meaning1502 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1498 = false ∨ valuation q 1502 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_right (literal (valuationOf q) (1499)) (literal (valuationOf q) (1503)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 1 (meaning1499 q) (meaning1503 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1503 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_right (literal (valuationOf q) (1500)) (literal (valuationOf q) (1504)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 2 (meaning1500 q) (meaning1504 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1504 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1505 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_right (literal (valuationOf q) (1501)) (literal (valuationOf q) (1505)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 3 (meaning1501 q) (meaning1505 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1505 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_left (literal (valuationOf q) (1492)) (literal (valuationOf q) (1503)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 1 (meaning1492 q) (meaning1503 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1503 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1504)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 1 1 (meaning1492 q) (meaning1499 q) (meaning1504 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1499 = false ∨ valuation q 1504 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1505 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1505)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 1 2 (meaning1492 q) (meaning1500 q) (meaning1505 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1500 = false ∨ valuation q 1505 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1506 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1506)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 1 3 (meaning1492 q) (meaning1501 q) (meaning1506 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1501 = false ∨ valuation q 1506 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1507 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1507)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 1 4 (meaning1492 q) (meaning1502 q) (meaning1507 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1502 = false ∨ valuation q 1507 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_left (literal (valuationOf q) (1493)) (literal (valuationOf q) (1504)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 2 (meaning1493 q) (meaning1504 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1504 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1505 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1505)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 2 1 (meaning1493 q) (meaning1499 q) (meaning1505 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1499 = false ∨ valuation q 1505 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1506 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1506)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 2 2 (meaning1493 q) (meaning1500 q) (meaning1506 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1500 = false ∨ valuation q 1506 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1507 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1507)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 2 3 (meaning1493 q) (meaning1501 q) (meaning1507 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1501 = false ∨ valuation q 1507 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1507 = true := by
  have hs : count1503 q = (countLit q [-58, -60, -63]) + (countLit q [-66, -68, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63]) (l₂ := [-66, -68, -69, -71])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1507)) (countLit q [-58, -60, -63]) (countLit q [-66, -68, -69, -71]) (count1503 q) 3 2 (meaning1494 q) (meaning1500 q) (meaning1507 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1500 = false ∨ valuation q 1507 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1510)) (countLit q [-76]) (countLit q [-77]) (count1510 q) 1 (meaningNeg77 q) (meaning1510 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1510 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1510)) (countLit q [-76]) (countLit q [-77]) (count1510 q) 1 (meaningNeg76 q) (meaning1510 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1510 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1511)) (countLit q [-76]) (countLit q [-77]) (count1510 q) 1 1 (meaningNeg76 q) (meaningNeg77 q) (meaning1511 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 77 = true ∨ valuation q 1511 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-72]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (1510)) (literal (valuationOf q) (1512)) (countLit q [-72]) (countLit q [-76, -77]) (count1512 q) 1 (meaning1510 q) (meaning1512 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1512 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-72]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (1511)) (literal (valuationOf q) (1513)) (countLit q [-72]) (countLit q [-76, -77]) (count1512 q) 2 (meaning1511 q) (meaning1513 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1513 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-72]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-76, -77])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1512)) (countLit q [-72]) (countLit q [-76, -77]) (count1512 q) 1 (meaningNeg72 q) (meaning1512 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1512 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1510 = false ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-72]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1513)) (countLit q [-72]) (countLit q [-76, -77]) (count1512 q) 1 1 (meaningNeg72 q) (meaning1510 q) (meaning1513 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1510 = false ∨ valuation q 1513 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1511 = false ∨ valuationOf q 1514 = true := by
  have hs : count1512 q = (countLit q [-72]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1514)) (countLit q [-72]) (countLit q [-76, -77]) (count1512 q) 1 2 (meaningNeg72 q) (meaning1511 q) (meaning1514 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1511 = false ∨ valuation q 1514 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1515 = true := by
  have hs : count1515 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1515)) (countLit q [-78]) (countLit q [-79]) (count1515 q) 1 (meaningNeg79 q) (meaning1515 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1515 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1515 = true := by
  have hs : count1515 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1515)) (countLit q [-78]) (countLit q [-79]) (count1515 q) 1 (meaningNeg78 q) (meaning1515 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1515 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E171.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112171
