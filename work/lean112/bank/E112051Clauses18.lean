import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 858 = true := by
  have hs : count857 q = (countLit q [-42]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-47, -48])
  have hm := merge_right (literal (valuationOf q) (856)) (literal (valuationOf q) (858)) (countLit q [-42]) (countLit q [-47, -48]) (count857 q) 2 (meaning856 q) (meaning858 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 858 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 857 = true := by
  have hs : count857 q = (countLit q [-42]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-47, -48])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (857)) (countLit q [-42]) (countLit q [-47, -48]) (count857 q) 1 (meaningNeg42 q) (meaning857 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 857 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 855 = false ∨ valuationOf q 858 = true := by
  have hs : count857 q = (countLit q [-42]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (855)) (literal (valuationOf q) (858)) (countLit q [-42]) (countLit q [-47, -48]) (count857 q) 1 1 (meaningNeg42 q) (meaning855 q) (meaning858 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 855 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 855 = false ∨ valuation q 858 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (860)) (countLit q [-49]) (countLit q [-51]) (count860 q) 1 (meaningNeg51 q) (meaning860 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 860 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (860)) (countLit q [-49]) (countLit q [-51]) (count860 q) 1 (meaningNeg49 q) (meaning860 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 860 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 51 = true ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (861)) (countLit q [-49]) (countLit q [-51]) (count860 q) 1 1 (meaningNeg49 q) (meaningNeg51 q) (meaning861 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 51 = true ∨ valuation q 861 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 862 = true := by
  have hs : count862 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (862)) (countLit q [-54]) (countLit q [-55]) (count862 q) 1 (meaningNeg55 q) (meaning862 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 862 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 862 = true := by
  have hs : count862 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (862)) (countLit q [-54]) (countLit q [-55]) (count862 q) 1 (meaningNeg54 q) (meaning862 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 862 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 55 = true ∨ valuationOf q 863 = true := by
  have hs : count862 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (863)) (countLit q [-54]) (countLit q [-55]) (count862 q) 1 1 (meaningNeg54 q) (meaningNeg55 q) (meaning863 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 863 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 864 = true := by
  have hs : count864 q = (countLit q [-49, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-54, -55])
  have hm := merge_right (literal (valuationOf q) (862)) (literal (valuationOf q) (864)) (countLit q [-49, -51]) (countLit q [-54, -55]) (count864 q) 1 (meaning862 q) (meaning864 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 864 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-49, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-54, -55])
  have hm := merge_right (literal (valuationOf q) (863)) (literal (valuationOf q) (865)) (countLit q [-49, -51]) (countLit q [-54, -55]) (count864 q) 2 (meaning863 q) (meaning865 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 865 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 864 = true := by
  have hs : count864 q = (countLit q [-49, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-54, -55])
  have hm := merge_left (literal (valuationOf q) (860)) (literal (valuationOf q) (864)) (countLit q [-49, -51]) (countLit q [-54, -55]) (count864 q) 1 (meaning860 q) (meaning864 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 864 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 862 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-49, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-54, -55])
  have hm := merge_two (literal (valuationOf q) (860)) (literal (valuationOf q) (862)) (literal (valuationOf q) (865)) (countLit q [-49, -51]) (countLit q [-54, -55]) (count864 q) 1 1 (meaning860 q) (meaning862 q) (meaning865 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 862 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 862 = false ∨ valuation q 865 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 863 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-49, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-54, -55])
  have hm := merge_two (literal (valuationOf q) (860)) (literal (valuationOf q) (863)) (literal (valuationOf q) (866)) (countLit q [-49, -51]) (countLit q [-54, -55]) (count864 q) 1 2 (meaning860 q) (meaning863 q) (meaning866 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 863 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 863 = false ∨ valuation q 866 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-49, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-54, -55])
  have hm := merge_left (literal (valuationOf q) (861)) (literal (valuationOf q) (865)) (countLit q [-49, -51]) (countLit q [-54, -55]) (count864 q) 2 (meaning861 q) (meaning865 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 865 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 868 = true := by
  have hs : count868 q = (countLit q [-42, -47, -48]) + (countLit q [-49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-42, -47, -48]) (l₂ := [-49, -51, -54, -55])
  have hm := merge_right (literal (valuationOf q) (864)) (literal (valuationOf q) (868)) (countLit q [-42, -47, -48]) (countLit q [-49, -51, -54, -55]) (count868 q) 1 (meaning864 q) (meaning868 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 868 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 869 = true := by
  have hs : count868 q = (countLit q [-42, -47, -48]) + (countLit q [-49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-42, -47, -48]) (l₂ := [-49, -51, -54, -55])
  have hm := merge_right (literal (valuationOf q) (865)) (literal (valuationOf q) (869)) (countLit q [-42, -47, -48]) (countLit q [-49, -51, -54, -55]) (count868 q) 2 (meaning865 q) (meaning869 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 869 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 870 = true := by
  have hs : count868 q = (countLit q [-42, -47, -48]) + (countLit q [-49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-42, -47, -48]) (l₂ := [-49, -51, -54, -55])
  have hm := merge_right (literal (valuationOf q) (866)) (literal (valuationOf q) (870)) (countLit q [-42, -47, -48]) (countLit q [-49, -51, -54, -55]) (count868 q) 3 (meaning866 q) (meaning870 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 870 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 868 = true := by
  have hs : count868 q = (countLit q [-42, -47, -48]) + (countLit q [-49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-42, -47, -48]) (l₂ := [-49, -51, -54, -55])
  have hm := merge_left (literal (valuationOf q) (857)) (literal (valuationOf q) (868)) (countLit q [-42, -47, -48]) (countLit q [-49, -51, -54, -55]) (count868 q) 1 (meaning857 q) (meaning868 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 868 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 864 = false ∨ valuationOf q 869 = true := by
  have hs : count868 q = (countLit q [-42, -47, -48]) + (countLit q [-49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-42, -47, -48]) (l₂ := [-49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (864)) (literal (valuationOf q) (869)) (countLit q [-42, -47, -48]) (countLit q [-49, -51, -54, -55]) (count868 q) 1 1 (meaning857 q) (meaning864 q) (meaning869 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 864 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 864 = false ∨ valuation q 869 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 865 = false ∨ valuationOf q 870 = true := by
  have hs : count868 q = (countLit q [-42, -47, -48]) + (countLit q [-49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-42, -47, -48]) (l₂ := [-49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (865)) (literal (valuationOf q) (870)) (countLit q [-42, -47, -48]) (countLit q [-49, -51, -54, -55]) (count868 q) 1 2 (meaning857 q) (meaning865 q) (meaning870 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 865 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 865 = false ∨ valuation q 870 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 866 = false ∨ valuationOf q 871 = true := by
  have hs : count868 q = (countLit q [-42, -47, -48]) + (countLit q [-49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-42, -47, -48]) (l₂ := [-49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (866)) (literal (valuationOf q) (871)) (countLit q [-42, -47, -48]) (countLit q [-49, -51, -54, -55]) (count868 q) 1 3 (meaning857 q) (meaning866 q) (meaning871 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 866 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 866 = false ∨ valuation q 871 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 864 = false ∨ valuationOf q 870 = true := by
  have hs : count868 q = (countLit q [-42, -47, -48]) + (countLit q [-49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-42, -47, -48]) (l₂ := [-49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (864)) (literal (valuationOf q) (870)) (countLit q [-42, -47, -48]) (countLit q [-49, -51, -54, -55]) (count868 q) 2 1 (meaning858 q) (meaning864 q) (meaning870 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 864 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 864 = false ∨ valuation q 870 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_right (literal (valuationOf q) (868)) (literal (valuationOf q) (875)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 1 (meaning868 q) (meaning875 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 875 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_right (literal (valuationOf q) (869)) (literal (valuationOf q) (876)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 2 (meaning869 q) (meaning876 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 876 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_left (literal (valuationOf q) (848)) (literal (valuationOf q) (875)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 1 (meaning848 q) (meaning875 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 875 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 868 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (868)) (literal (valuationOf q) (876)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 1 1 (meaning848 q) (meaning868 q) (meaning876 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 868 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 868 = false ∨ valuation q 876 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 869 = false ∨ valuationOf q 877 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (869)) (literal (valuationOf q) (877)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 1 2 (meaning848 q) (meaning869 q) (meaning877 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 869 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 869 = false ∨ valuation q 877 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 870 = false ∨ valuationOf q 878 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (870)) (literal (valuationOf q) (878)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 1 3 (meaning848 q) (meaning870 q) (meaning878 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 870 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 870 = false ∨ valuation q 878 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_left (literal (valuationOf q) (849)) (literal (valuationOf q) (876)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 2 (meaning849 q) (meaning876 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 876 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 868 = false ∨ valuationOf q 877 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (849)) (literal (valuationOf q) (868)) (literal (valuationOf q) (877)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 2 1 (meaning849 q) (meaning868 q) (meaning877 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 868 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 868 = false ∨ valuation q 877 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 869 = false ∨ valuationOf q 878 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (849)) (literal (valuationOf q) (869)) (literal (valuationOf q) (878)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 2 2 (meaning849 q) (meaning869 q) (meaning878 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 869 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 869 = false ∨ valuation q 878 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E051.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112051
