import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 3 5 (meaning1443 q) (meaning1499 q) (meaning1516 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1499 = false ∨ valuation q 1516 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 3 6 (meaning1443 q) (meaning1500 q) (meaning1517 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1500 = false ∨ valuation q 1517 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1518 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 3 7 (meaning1443 q) (meaning1501 q) (meaning1518 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1501 = false ∨ valuation q 1518 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1514 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1514)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 4 2 (meaning1444 q) (meaning1496 q) (meaning1514 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1496 = false ∨ valuation q 1514 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1515 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1515)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 4 3 (meaning1444 q) (meaning1497 q) (meaning1515 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1497 = false ∨ valuation q 1515 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 4 4 (meaning1444 q) (meaning1498 q) (meaning1516 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1498 = false ∨ valuation q 1516 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 4 5 (meaning1444 q) (meaning1499 q) (meaning1517 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1499 = false ∨ valuation q 1517 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1518 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 4 6 (meaning1444 q) (meaning1500 q) (meaning1518 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1500 = false ∨ valuation q 1518 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1515 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1515)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 5 2 (meaning1445 q) (meaning1496 q) (meaning1515 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1496 = false ∨ valuation q 1515 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 5 3 (meaning1445 q) (meaning1497 q) (meaning1516 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1497 = false ∨ valuation q 1516 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 5 4 (meaning1445 q) (meaning1498 q) (meaning1517 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1498 = false ∨ valuation q 1517 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1518 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 5 5 (meaning1445 q) (meaning1499 q) (meaning1518 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1499 = false ∨ valuation q 1518 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 6 2 (meaning1446 q) (meaning1496 q) (meaning1516 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1496 = false ∨ valuation q 1516 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 6 3 (meaning1446 q) (meaning1497 q) (meaning1517 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1497 = false ∨ valuation q 1517 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1518 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 6 4 (meaning1446 q) (meaning1498 q) (meaning1518 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1498 = false ∨ valuation q 1518 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 7 2 (meaning1447 q) (meaning1496 q) (meaning1517 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1496 = false ∨ valuation q 1517 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1519 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 7 4 (meaning1447 q) (meaning1498 q) (meaning1519 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1498 = false ∨ valuation q 1519 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-59]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1526)) (countLit q [-59]) (countLit q [-62]) (count1526 q) 1 (meaningNeg62 q) (meaning1526 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1526 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-59]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1526)) (countLit q [-59]) (countLit q [-62]) (count1526 q) 1 (meaningNeg59 q) (meaning1526 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1526 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 62 = true ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-59]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (1527)) (countLit q [-59]) (countLit q [-62]) (count1526 q) 1 1 (meaningNeg59 q) (meaningNeg62 q) (meaning1527 q) hs
  change (! (valuationOf q 59)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 62 = true ∨ valuation q 1527 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -62])
  have hm := merge_right (literal (valuationOf q) (1526)) (literal (valuationOf q) (1528)) (countLit q [-58]) (countLit q [-59, -62]) (count1528 q) 1 (meaning1526 q) (meaning1528 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1528 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -62])
  have hm := merge_right (literal (valuationOf q) (1527)) (literal (valuationOf q) (1529)) (countLit q [-58]) (countLit q [-59, -62]) (count1528 q) 2 (meaning1527 q) (meaning1529 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1529 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -62])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1528)) (countLit q [-58]) (countLit q [-59, -62]) (count1528 q) 1 (meaningNeg58 q) (meaning1528 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1528 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1526 = false ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -62])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1529)) (countLit q [-58]) (countLit q [-59, -62]) (count1528 q) 1 1 (meaningNeg58 q) (meaning1526 q) (meaning1529 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1526 = false ∨ valuation q 1529 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1527 = false ∨ valuationOf q 1530 = true := by
  have hs : count1528 q = (countLit q [-58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -62])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1530)) (countLit q [-58]) (countLit q [-59, -62]) (count1528 q) 1 2 (meaningNeg58 q) (meaning1527 q) (meaning1530 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1527 = false ∨ valuation q 1530 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1531)) (countLit q [-66]) (countLit q [-67]) (count1531 q) 1 (meaningNeg67 q) (meaning1531 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1531 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1531)) (countLit q [-66]) (countLit q [-67]) (count1531 q) 1 (meaningNeg66 q) (meaning1531 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1531 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 67 = true ∨ valuationOf q 1532 = true := by
  have hs : count1531 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-66)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (1532)) (countLit q [-66]) (countLit q [-67]) (count1531 q) 1 1 (meaningNeg66 q) (meaningNeg67 q) (meaning1532 q) hs
  change (! (valuationOf q 66)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 1532 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (1533)) (countLit q [-70]) (countLit q [-72]) (count1533 q) 1 (meaningNeg72 q) (meaning1533 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1533 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1533)) (countLit q [-70]) (countLit q [-72]) (count1533 q) 1 (meaningNeg70 q) (meaning1533 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1533 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 72 = true ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-72)) (literal (valuationOf q) (1534)) (countLit q [-70]) (countLit q [-72]) (count1533 q) 1 1 (meaningNeg70 q) (meaningNeg72 q) (meaning1534 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 72)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 72 = true ∨ valuation q 1534 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-66, -67]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-70, -72])
  have hm := merge_right (literal (valuationOf q) (1533)) (literal (valuationOf q) (1535)) (countLit q [-66, -67]) (countLit q [-70, -72]) (count1535 q) 1 (meaning1533 q) (meaning1535 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1535 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E058.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112058
