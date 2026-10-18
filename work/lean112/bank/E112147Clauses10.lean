import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 685 = true := by
  have hs : count685 q = (countLit q [-14]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (685)) (countLit q [-14]) (countLit q [-18]) (count685 q) 1 (meaningNeg14 q) (meaning685 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 685 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 685 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 18 = true ∨ valuationOf q 686 = true := by
  have hs : count685 q = (countLit q [-14]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (686)) (countLit q [-14]) (countLit q [-18]) (count685 q) 1 1 (meaningNeg14 q) (meaningNeg18 q) (meaning686 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 686 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 18 = true ∨ valuation q 686 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 685 = false ∨ valuationOf q 687 = true := by
  have hs : count687 q = (countLit q [-13]) + (countLit q [-14, -18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -18])
  have hm := merge_right (literal (valuationOf q) (685)) (literal (valuationOf q) (687)) (countLit q [-13]) (countLit q [-14, -18]) (count687 q) 1 (meaning685 q) (meaning687 q) hs
  change valuationOf q 685 = false ∨ valuationOf q 687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 685 = false ∨ valuation q 687 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 686 = false ∨ valuationOf q 688 = true := by
  have hs : count687 q = (countLit q [-13]) + (countLit q [-14, -18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -18])
  have hm := merge_right (literal (valuationOf q) (686)) (literal (valuationOf q) (688)) (countLit q [-13]) (countLit q [-14, -18]) (count687 q) 2 (meaning686 q) (meaning688 q) hs
  change valuationOf q 686 = false ∨ valuationOf q 688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 686 = false ∨ valuation q 688 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 687 = true := by
  have hs : count687 q = (countLit q [-13]) + (countLit q [-14, -18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -18])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (687)) (countLit q [-13]) (countLit q [-14, -18]) (count687 q) 1 (meaningNeg13 q) (meaning687 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 687 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 687 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 685 = false ∨ valuationOf q 688 = true := by
  have hs : count687 q = (countLit q [-13]) + (countLit q [-14, -18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -18])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (685)) (literal (valuationOf q) (688)) (countLit q [-13]) (countLit q [-14, -18]) (count687 q) 1 1 (meaningNeg13 q) (meaning685 q) (meaning688 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 685 = false ∨ valuationOf q 688 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 685 = false ∨ valuation q 688 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 686 = false ∨ valuationOf q 689 = true := by
  have hs : count687 q = (countLit q [-13]) + (countLit q [-14, -18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -18])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (686)) (literal (valuationOf q) (689)) (countLit q [-13]) (countLit q [-14, -18]) (count687 q) 1 2 (meaningNeg13 q) (meaning686 q) (meaning689 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 686 = false ∨ valuationOf q 689 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 686 = false ∨ valuation q 689 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 690 = true := by
  have hs : count690 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (690)) (countLit q [-22]) (countLit q [-25]) (count690 q) 1 (meaningNeg25 q) (meaning690 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 690 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 690 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 690 = true := by
  have hs : count690 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (690)) (countLit q [-22]) (countLit q [-25]) (count690 q) 1 (meaningNeg22 q) (meaning690 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 690 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 690 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 25 = true ∨ valuationOf q 691 = true := by
  have hs : count690 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (691)) (countLit q [-22]) (countLit q [-25]) (count690 q) 1 1 (meaningNeg22 q) (meaningNeg25 q) (meaning691 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 691 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 25 = true ∨ valuation q 691 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 690 = false ∨ valuationOf q 692 = true := by
  have hs : count692 q = (countLit q [-21]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22, -25])
  have hm := merge_right (literal (valuationOf q) (690)) (literal (valuationOf q) (692)) (countLit q [-21]) (countLit q [-22, -25]) (count692 q) 1 (meaning690 q) (meaning692 q) hs
  change valuationOf q 690 = false ∨ valuationOf q 692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 690 = false ∨ valuation q 692 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 691 = false ∨ valuationOf q 693 = true := by
  have hs : count692 q = (countLit q [-21]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22, -25])
  have hm := merge_right (literal (valuationOf q) (691)) (literal (valuationOf q) (693)) (countLit q [-21]) (countLit q [-22, -25]) (count692 q) 2 (meaning691 q) (meaning693 q) hs
  change valuationOf q 691 = false ∨ valuationOf q 693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 691 = false ∨ valuation q 693 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 692 = true := by
  have hs : count692 q = (countLit q [-21]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22, -25])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (692)) (countLit q [-21]) (countLit q [-22, -25]) (count692 q) 1 (meaningNeg21 q) (meaning692 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 692 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 692 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 690 = false ∨ valuationOf q 693 = true := by
  have hs : count692 q = (countLit q [-21]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22, -25])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (690)) (literal (valuationOf q) (693)) (countLit q [-21]) (countLit q [-22, -25]) (count692 q) 1 1 (meaningNeg21 q) (meaning690 q) (meaning693 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 690 = false ∨ valuationOf q 693 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 690 = false ∨ valuation q 693 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 692 = false ∨ valuationOf q 695 = true := by
  have hs : count695 q = (countLit q [-13, -14, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_right (literal (valuationOf q) (692)) (literal (valuationOf q) (695)) (countLit q [-13, -14, -18]) (countLit q [-21, -22, -25]) (count695 q) 1 (meaning692 q) (meaning695 q) hs
  change valuationOf q 692 = false ∨ valuationOf q 695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 692 = false ∨ valuation q 695 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 687 = false ∨ valuationOf q 695 = true := by
  have hs : count695 q = (countLit q [-13, -14, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_left (literal (valuationOf q) (687)) (literal (valuationOf q) (695)) (countLit q [-13, -14, -18]) (countLit q [-21, -22, -25]) (count695 q) 1 (meaning687 q) (meaning695 q) hs
  change valuationOf q 687 = false ∨ valuationOf q 695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 687 = false ∨ valuation q 695 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 687 = false ∨ valuationOf q 692 = false ∨ valuationOf q 696 = true := by
  have hs : count695 q = (countLit q [-13, -14, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (687)) (literal (valuationOf q) (692)) (literal (valuationOf q) (696)) (countLit q [-13, -14, -18]) (countLit q [-21, -22, -25]) (count695 q) 1 1 (meaning687 q) (meaning692 q) (meaning696 q) hs
  change valuationOf q 687 = false ∨ valuationOf q 692 = false ∨ valuationOf q 696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 687 = false ∨ valuation q 692 = false ∨ valuation q 696 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 687 = false ∨ valuationOf q 693 = false ∨ valuationOf q 697 = true := by
  have hs : count695 q = (countLit q [-13, -14, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (687)) (literal (valuationOf q) (693)) (literal (valuationOf q) (697)) (countLit q [-13, -14, -18]) (countLit q [-21, -22, -25]) (count695 q) 1 2 (meaning687 q) (meaning693 q) (meaning697 q) hs
  change valuationOf q 687 = false ∨ valuationOf q 693 = false ∨ valuationOf q 697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 687 = false ∨ valuation q 693 = false ∨ valuation q 697 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 688 = false ∨ valuationOf q 696 = true := by
  have hs : count695 q = (countLit q [-13, -14, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_left (literal (valuationOf q) (688)) (literal (valuationOf q) (696)) (countLit q [-13, -14, -18]) (countLit q [-21, -22, -25]) (count695 q) 2 (meaning688 q) (meaning696 q) hs
  change valuationOf q 688 = false ∨ valuationOf q 696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 688 = false ∨ valuation q 696 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 688 = false ∨ valuationOf q 692 = false ∨ valuationOf q 697 = true := by
  have hs : count695 q = (countLit q [-13, -14, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (688)) (literal (valuationOf q) (692)) (literal (valuationOf q) (697)) (countLit q [-13, -14, -18]) (countLit q [-21, -22, -25]) (count695 q) 2 1 (meaning688 q) (meaning692 q) (meaning697 q) hs
  change valuationOf q 688 = false ∨ valuationOf q 692 = false ∨ valuationOf q 697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 688 = false ∨ valuation q 692 = false ∨ valuation q 697 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 689 = false ∨ valuationOf q 697 = true := by
  have hs : count695 q = (countLit q [-13, -14, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_left (literal (valuationOf q) (689)) (literal (valuationOf q) (697)) (countLit q [-13, -14, -18]) (countLit q [-21, -22, -25]) (count695 q) 3 (meaning689 q) (meaning697 q) hs
  change valuationOf q 689 = false ∨ valuationOf q 697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 689 = false ∨ valuation q 697 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 679 = false ∨ valuationOf q 695 = false ∨ valuationOf q 702 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (679)) (literal (valuationOf q) (695)) (literal (valuationOf q) (702)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 1 1 (meaning679 q) (meaning695 q) (meaning702 q) hs
  change valuationOf q 679 = false ∨ valuationOf q 695 = false ∨ valuationOf q 702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 679 = false ∨ valuation q 695 = false ∨ valuation q 702 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 679 = false ∨ valuationOf q 696 = false ∨ valuationOf q 703 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (679)) (literal (valuationOf q) (696)) (literal (valuationOf q) (703)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 1 2 (meaning679 q) (meaning696 q) (meaning703 q) hs
  change valuationOf q 679 = false ∨ valuationOf q 696 = false ∨ valuationOf q 703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 679 = false ∨ valuation q 696 = false ∨ valuation q 703 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 679 = false ∨ valuationOf q 697 = false ∨ valuationOf q 704 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (679)) (literal (valuationOf q) (697)) (literal (valuationOf q) (704)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 1 3 (meaning679 q) (meaning697 q) (meaning704 q) hs
  change valuationOf q 679 = false ∨ valuationOf q 697 = false ∨ valuationOf q 704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 679 = false ∨ valuation q 697 = false ∨ valuation q 704 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 680 = false ∨ valuationOf q 695 = false ∨ valuationOf q 703 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (680)) (literal (valuationOf q) (695)) (literal (valuationOf q) (703)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 2 1 (meaning680 q) (meaning695 q) (meaning703 q) hs
  change valuationOf q 680 = false ∨ valuationOf q 695 = false ∨ valuationOf q 703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 680 = false ∨ valuation q 695 = false ∨ valuation q 703 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 680 = false ∨ valuationOf q 696 = false ∨ valuationOf q 704 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (680)) (literal (valuationOf q) (696)) (literal (valuationOf q) (704)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 2 2 (meaning680 q) (meaning696 q) (meaning704 q) hs
  change valuationOf q 680 = false ∨ valuationOf q 696 = false ∨ valuationOf q 704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 680 = false ∨ valuation q 696 = false ∨ valuation q 704 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 680 = false ∨ valuationOf q 697 = false ∨ valuationOf q 705 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (680)) (literal (valuationOf q) (697)) (literal (valuationOf q) (705)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 2 3 (meaning680 q) (meaning697 q) (meaning705 q) hs
  change valuationOf q 680 = false ∨ valuationOf q 697 = false ∨ valuationOf q 705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 680 = false ∨ valuation q 697 = false ∨ valuation q 705 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 681 = false ∨ valuationOf q 695 = false ∨ valuationOf q 704 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (681)) (literal (valuationOf q) (695)) (literal (valuationOf q) (704)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 3 1 (meaning681 q) (meaning695 q) (meaning704 q) hs
  change valuationOf q 681 = false ∨ valuationOf q 695 = false ∨ valuationOf q 704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 681 = false ∨ valuation q 695 = false ∨ valuation q 704 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 681 = false ∨ valuationOf q 696 = false ∨ valuationOf q 705 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (681)) (literal (valuationOf q) (696)) (literal (valuationOf q) (705)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 3 2 (meaning681 q) (meaning696 q) (meaning705 q) hs
  change valuationOf q 681 = false ∨ valuationOf q 696 = false ∨ valuationOf q 705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 681 = false ∨ valuation q 696 = false ∨ valuation q 705 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 681 = false ∨ valuationOf q 697 = false ∨ valuationOf q 706 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (681)) (literal (valuationOf q) (697)) (literal (valuationOf q) (706)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 3 3 (meaning681 q) (meaning697 q) (meaning706 q) hs
  change valuationOf q 681 = false ∨ valuationOf q 697 = false ∨ valuationOf q 706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 681 = false ∨ valuation q 697 = false ∨ valuation q 706 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 682 = false ∨ valuationOf q 704 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_left (literal (valuationOf q) (682)) (literal (valuationOf q) (704)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 4 (meaning682 q) (meaning704 q) hs
  change valuationOf q 682 = false ∨ valuationOf q 704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 682 = false ∨ valuation q 704 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 682 = false ∨ valuationOf q 695 = false ∨ valuationOf q 705 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (682)) (literal (valuationOf q) (695)) (literal (valuationOf q) (705)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 4 1 (meaning682 q) (meaning695 q) (meaning705 q) hs
  change valuationOf q 682 = false ∨ valuationOf q 695 = false ∨ valuationOf q 705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 682 = false ∨ valuation q 695 = false ∨ valuation q 705 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E147.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112147
