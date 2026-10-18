import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -13])
  have hm := merge_right (literal (valuationOf q) (1504)) (literal (valuationOf q) (1506)) (countLit q [-6, -8]) (countLit q [-10, -13]) (count1506 q) 1 (meaning1504 q) (meaning1506 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1506 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -13])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (countLit q [-6, -8]) (countLit q [-10, -13]) (count1506 q) 2 (meaning1505 q) (meaning1507 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -13])
  have hm := merge_left (literal (valuationOf q) (1502)) (literal (valuationOf q) (1506)) (countLit q [-6, -8]) (countLit q [-10, -13]) (count1506 q) 1 (meaning1502 q) (meaning1506 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1506 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -13])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1507)) (countLit q [-6, -8]) (countLit q [-10, -13]) (count1506 q) 1 1 (meaning1502 q) (meaning1504 q) (meaning1507 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = false ∨ valuation q 1507 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -13])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1508)) (countLit q [-6, -8]) (countLit q [-10, -13]) (count1506 q) 1 2 (meaning1502 q) (meaning1505 q) (meaning1508 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1505 = false ∨ valuation q 1508 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1511)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -13]) (count1510 q) 1 1 (meaning1499 q) (meaning1506 q) (meaning1511 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1506 = false ∨ valuation q 1511 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1512)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -13]) (count1510 q) 1 2 (meaning1499 q) (meaning1507 q) (meaning1512 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1507 = false ∨ valuation q 1512 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1513)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -13]) (count1510 q) 1 3 (meaning1499 q) (meaning1508 q) (meaning1513 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1508 = false ∨ valuation q 1513 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -13])
  have hm := merge_left (literal (valuationOf q) (1500)) (literal (valuationOf q) (1511)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -13]) (count1510 q) 2 (meaning1500 q) (meaning1511 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1511 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1512)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -13]) (count1510 q) 2 1 (meaning1500 q) (meaning1506 q) (meaning1512 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1506 = false ∨ valuation q 1512 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1513)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -13]) (count1510 q) 2 2 (meaning1500 q) (meaning1507 q) (meaning1513 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1507 = false ∨ valuation q 1513 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true := by
  have hs : count1510 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -13]) (count1510 q) 2 3 (meaning1500 q) (meaning1508 q) (meaning1514 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1508 = false ∨ valuation q 1514 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -13])
  have hm := merge_left (literal (valuationOf q) (1501)) (literal (valuationOf q) (1512)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -13]) (count1510 q) 3 (meaning1501 q) (meaning1512 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1512 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1513)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -13]) (count1510 q) 3 1 (meaning1501 q) (meaning1506 q) (meaning1513 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1506 = false ∨ valuation q 1513 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1514 = true := by
  have hs : count1510 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1514)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -13]) (count1510 q) 3 2 (meaning1501 q) (meaning1507 q) (meaning1514 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1507 = false ∨ valuation q 1514 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-15]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16])
  have hm := merge_right (literal (valuationOf q) (-16)) (literal (valuationOf q) (1517)) (countLit q [-15]) (countLit q [-16]) (count1517 q) 1 (meaningNeg16 q) (meaning1517 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1517 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-15]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1517)) (countLit q [-15]) (countLit q [-16]) (count1517 q) 1 (meaningNeg15 q) (meaning1517 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1517 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 16 = true ∨ valuationOf q 1518 = true := by
  have hs : count1517 q = (countLit q [-15]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-16)) (literal (valuationOf q) (1518)) (countLit q [-15]) (countLit q [-16]) (count1517 q) 1 1 (meaningNeg15 q) (meaningNeg16 q) (meaning1518 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 16)) = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 1518 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1519)) (countLit q [-17]) (countLit q [-19]) (count1519 q) 1 (meaningNeg19 q) (meaning1519 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1519 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1519)) (countLit q [-17]) (countLit q [-19]) (count1519 q) 1 (meaningNeg17 q) (meaning1519 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1519 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 19 = true ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (1520)) (countLit q [-17]) (countLit q [-19]) (count1519 q) 1 1 (meaningNeg17 q) (meaningNeg19 q) (meaning1520 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 1520 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-15, -16]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-17, -19])
  have hm := merge_right (literal (valuationOf q) (1519)) (literal (valuationOf q) (1521)) (countLit q [-15, -16]) (countLit q [-17, -19]) (count1521 q) 1 (meaning1519 q) (meaning1521 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1521 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1522 = true := by
  have hs : count1521 q = (countLit q [-15, -16]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-17, -19])
  have hm := merge_right (literal (valuationOf q) (1520)) (literal (valuationOf q) (1522)) (countLit q [-15, -16]) (countLit q [-17, -19]) (count1521 q) 2 (meaning1520 q) (meaning1522 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1522 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-15, -16]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-17, -19])
  have hm := merge_left (literal (valuationOf q) (1517)) (literal (valuationOf q) (1521)) (countLit q [-15, -16]) (countLit q [-17, -19]) (count1521 q) 1 (meaning1517 q) (meaning1521 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1521 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1522 = true := by
  have hs : count1521 q = (countLit q [-15, -16]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-17, -19])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1522)) (countLit q [-15, -16]) (countLit q [-17, -19]) (count1521 q) 1 1 (meaning1517 q) (meaning1519 q) (meaning1522 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1519 = false ∨ valuation q 1522 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1523 = true := by
  have hs : count1521 q = (countLit q [-15, -16]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-17, -19])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1523)) (countLit q [-15, -16]) (countLit q [-17, -19]) (count1521 q) 1 2 (meaning1517 q) (meaning1520 q) (meaning1523 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1520 = false ∨ valuation q 1523 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1522 = true := by
  have hs : count1521 q = (countLit q [-15, -16]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-17, -19])
  have hm := merge_left (literal (valuationOf q) (1518)) (literal (valuationOf q) (1522)) (countLit q [-15, -16]) (countLit q [-17, -19]) (count1521 q) 2 (meaning1518 q) (meaning1522 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1522 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1523 = true := by
  have hs : count1521 q = (countLit q [-15, -16]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-17, -19])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1523)) (countLit q [-15, -16]) (countLit q [-17, -19]) (count1521 q) 2 1 (meaning1518 q) (meaning1519 q) (meaning1523 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1519 = false ∨ valuation q 1523 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1524 = true := by
  have hs : count1521 q = (countLit q [-15, -16]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15, -16]) (l₂ := [-17, -19])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1524)) (countLit q [-15, -16]) (countLit q [-17, -19]) (count1521 q) 2 2 (meaning1518 q) (meaning1520 q) (meaning1524 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1520 = false ∨ valuation q 1524 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1525 = true := by
  have hs : count1525 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1525)) (countLit q [-22]) (countLit q [-25]) (count1525 q) 1 (meaningNeg25 q) (meaning1525 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1525 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1525 = true := by
  have hs : count1525 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1525)) (countLit q [-22]) (countLit q [-25]) (count1525 q) 1 (meaningNeg22 q) (meaning1525 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1525 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 25 = true ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (1526)) (countLit q [-22]) (countLit q [-25]) (count1525 q) 1 1 (meaningNeg22 q) (meaningNeg25 q) (meaning1526 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 25 = true ∨ valuation q 1526 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E186.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112186
