import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 728 = false ∨ valuationOf q 731 = true := by
  have hs : count729 q = (countLit q [-1]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (728)) (literal (valuationOf q) (731)) (countLit q [-1]) (countLit q [-3, -5]) (count729 q) 1 2 (meaningNeg1 q) (meaning728 q) (meaning731 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 728 = false ∨ valuationOf q 731 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 728 = false ∨ valuation q 731 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 732 = true := by
  have hs : count732 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (732)) (countLit q [-9]) (countLit q [-10]) (count732 q) 1 (meaningNeg10 q) (meaning732 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 732 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 732 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 732 = true := by
  have hs : count732 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (732)) (countLit q [-9]) (countLit q [-10]) (count732 q) 1 (meaningNeg9 q) (meaning732 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 732 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 732 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 732 = false ∨ valuationOf q 734 = true := by
  have hs : count734 q = (countLit q [-7]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9, -10])
  have hm := merge_right (literal (valuationOf q) (732)) (literal (valuationOf q) (734)) (countLit q [-7]) (countLit q [-9, -10]) (count734 q) 1 (meaning732 q) (meaning734 q) hs
  change valuationOf q 732 = false ∨ valuationOf q 734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 732 = false ∨ valuation q 734 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 729 = false ∨ valuationOf q 737 = true := by
  have hs : count737 q = (countLit q [-1, -3, -5]) + (countLit q [-7, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-7, -9, -10])
  have hm := merge_left (literal (valuationOf q) (729)) (literal (valuationOf q) (737)) (countLit q [-1, -3, -5]) (countLit q [-7, -9, -10]) (count737 q) 1 (meaning729 q) (meaning737 q) hs
  change valuationOf q 729 = false ∨ valuationOf q 737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 729 = false ∨ valuation q 737 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 729 = false ∨ valuationOf q 734 = false ∨ valuationOf q 738 = true := by
  have hs : count737 q = (countLit q [-1, -3, -5]) + (countLit q [-7, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-7, -9, -10])
  have hm := merge_two (literal (valuationOf q) (729)) (literal (valuationOf q) (734)) (literal (valuationOf q) (738)) (countLit q [-1, -3, -5]) (countLit q [-7, -9, -10]) (count737 q) 1 1 (meaning729 q) (meaning734 q) (meaning738 q) hs
  change valuationOf q 729 = false ∨ valuationOf q 734 = false ∨ valuationOf q 738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 729 = false ∨ valuation q 734 = false ∨ valuation q 738 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 730 = false ∨ valuationOf q 738 = true := by
  have hs : count737 q = (countLit q [-1, -3, -5]) + (countLit q [-7, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-7, -9, -10])
  have hm := merge_left (literal (valuationOf q) (730)) (literal (valuationOf q) (738)) (countLit q [-1, -3, -5]) (countLit q [-7, -9, -10]) (count737 q) 2 (meaning730 q) (meaning738 q) hs
  change valuationOf q 730 = false ∨ valuationOf q 738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 730 = false ∨ valuation q 738 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 730 = false ∨ valuationOf q 734 = false ∨ valuationOf q 739 = true := by
  have hs : count737 q = (countLit q [-1, -3, -5]) + (countLit q [-7, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-7, -9, -10])
  have hm := merge_two (literal (valuationOf q) (730)) (literal (valuationOf q) (734)) (literal (valuationOf q) (739)) (countLit q [-1, -3, -5]) (countLit q [-7, -9, -10]) (count737 q) 2 1 (meaning730 q) (meaning734 q) (meaning739 q) hs
  change valuationOf q 730 = false ∨ valuationOf q 734 = false ∨ valuationOf q 739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 730 = false ∨ valuation q 734 = false ∨ valuation q 739 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 731 = false ∨ valuationOf q 739 = true := by
  have hs : count737 q = (countLit q [-1, -3, -5]) + (countLit q [-7, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-7, -9, -10])
  have hm := merge_left (literal (valuationOf q) (731)) (literal (valuationOf q) (739)) (countLit q [-1, -3, -5]) (countLit q [-7, -9, -10]) (count737 q) 3 (meaning731 q) (meaning739 q) hs
  change valuationOf q 731 = false ∨ valuationOf q 739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 731 = false ∨ valuation q 739 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 743 = true := by
  have hs : count743 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (743)) (countLit q [-14]) (countLit q [-17]) (count743 q) 1 (meaningNeg17 q) (meaning743 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 743 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 743 = true := by
  have hs : count743 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (743)) (countLit q [-14]) (countLit q [-17]) (count743 q) 1 (meaningNeg14 q) (meaning743 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 743 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 17 = true ∨ valuationOf q 744 = true := by
  have hs : count743 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (744)) (countLit q [-14]) (countLit q [-17]) (count743 q) 1 1 (meaningNeg14 q) (meaningNeg17 q) (meaning744 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 744 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 744 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 743 = false ∨ valuationOf q 745 = true := by
  have hs : count745 q = (countLit q [-13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -17])
  have hm := merge_right (literal (valuationOf q) (743)) (literal (valuationOf q) (745)) (countLit q [-13]) (countLit q [-14, -17]) (count745 q) 1 (meaning743 q) (meaning745 q) hs
  change valuationOf q 743 = false ∨ valuationOf q 745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 743 = false ∨ valuation q 745 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 744 = false ∨ valuationOf q 746 = true := by
  have hs : count745 q = (countLit q [-13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -17])
  have hm := merge_right (literal (valuationOf q) (744)) (literal (valuationOf q) (746)) (countLit q [-13]) (countLit q [-14, -17]) (count745 q) 2 (meaning744 q) (meaning746 q) hs
  change valuationOf q 744 = false ∨ valuationOf q 746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 744 = false ∨ valuation q 746 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 745 = true := by
  have hs : count745 q = (countLit q [-13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -17])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (745)) (countLit q [-13]) (countLit q [-14, -17]) (count745 q) 1 (meaningNeg13 q) (meaning745 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 745 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 745 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 743 = false ∨ valuationOf q 746 = true := by
  have hs : count745 q = (countLit q [-13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -17])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (743)) (literal (valuationOf q) (746)) (countLit q [-13]) (countLit q [-14, -17]) (count745 q) 1 1 (meaningNeg13 q) (meaning743 q) (meaning746 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 743 = false ∨ valuationOf q 746 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 743 = false ∨ valuation q 746 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 748 = true := by
  have hs : count748 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (748)) (countLit q [-20]) (countLit q [-22]) (count748 q) 1 (meaningNeg22 q) (meaning748 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 748 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 748 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 748 = true := by
  have hs : count748 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (748)) (countLit q [-20]) (countLit q [-22]) (count748 q) 1 (meaningNeg20 q) (meaning748 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 748 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 748 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 22 = true ∨ valuationOf q 749 = true := by
  have hs : count748 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (749)) (countLit q [-20]) (countLit q [-22]) (count748 q) 1 1 (meaningNeg20 q) (meaningNeg22 q) (meaning749 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 749 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 749 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 750 = true := by
  have hs : count750 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (750)) (countLit q [-24]) (countLit q [-25]) (count750 q) 1 (meaningNeg25 q) (meaning750 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 750 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 750 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 750 = true := by
  have hs : count750 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (750)) (countLit q [-24]) (countLit q [-25]) (count750 q) 1 (meaningNeg24 q) (meaning750 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 750 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 750 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 750 = false ∨ valuationOf q 752 = true := by
  have hs : count752 q = (countLit q [-20, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-24, -25])
  have hm := merge_right (literal (valuationOf q) (750)) (literal (valuationOf q) (752)) (countLit q [-20, -22]) (countLit q [-24, -25]) (count752 q) 1 (meaning750 q) (meaning752 q) hs
  change valuationOf q 750 = false ∨ valuationOf q 752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 750 = false ∨ valuation q 752 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 748 = false ∨ valuationOf q 752 = true := by
  have hs : count752 q = (countLit q [-20, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-24, -25])
  have hm := merge_left (literal (valuationOf q) (748)) (literal (valuationOf q) (752)) (countLit q [-20, -22]) (countLit q [-24, -25]) (count752 q) 1 (meaning748 q) (meaning752 q) hs
  change valuationOf q 748 = false ∨ valuationOf q 752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 748 = false ∨ valuation q 752 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 748 = false ∨ valuationOf q 750 = false ∨ valuationOf q 753 = true := by
  have hs : count752 q = (countLit q [-20, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (748)) (literal (valuationOf q) (750)) (literal (valuationOf q) (753)) (countLit q [-20, -22]) (countLit q [-24, -25]) (count752 q) 1 1 (meaning748 q) (meaning750 q) (meaning753 q) hs
  change valuationOf q 748 = false ∨ valuationOf q 750 = false ∨ valuationOf q 753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 748 = false ∨ valuation q 750 = false ∨ valuation q 753 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 749 = false ∨ valuationOf q 753 = true := by
  have hs : count752 q = (countLit q [-20, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-24, -25])
  have hm := merge_left (literal (valuationOf q) (749)) (literal (valuationOf q) (753)) (countLit q [-20, -22]) (countLit q [-24, -25]) (count752 q) 2 (meaning749 q) (meaning753 q) hs
  change valuationOf q 749 = false ∨ valuationOf q 753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 749 = false ∨ valuation q 753 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 749 = false ∨ valuationOf q 750 = false ∨ valuationOf q 754 = true := by
  have hs : count752 q = (countLit q [-20, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (749)) (literal (valuationOf q) (750)) (literal (valuationOf q) (754)) (countLit q [-20, -22]) (countLit q [-24, -25]) (count752 q) 2 1 (meaning749 q) (meaning750 q) (meaning754 q) hs
  change valuationOf q 749 = false ∨ valuationOf q 750 = false ∨ valuationOf q 754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 749 = false ∨ valuation q 750 = false ∨ valuation q 754 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 752 = false ∨ valuationOf q 756 = true := by
  have hs : count756 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (752)) (literal (valuationOf q) (756)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -24, -25]) (count756 q) 1 (meaning752 q) (meaning756 q) hs
  change valuationOf q 752 = false ∨ valuationOf q 756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 752 = false ∨ valuation q 756 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 753 = false ∨ valuationOf q 757 = true := by
  have hs : count756 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (753)) (literal (valuationOf q) (757)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -24, -25]) (count756 q) 2 (meaning753 q) (meaning757 q) hs
  change valuationOf q 753 = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 753 = false ∨ valuation q 757 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 745 = false ∨ valuationOf q 756 = true := by
  have hs : count756 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_left (literal (valuationOf q) (745)) (literal (valuationOf q) (756)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -24, -25]) (count756 q) 1 (meaning745 q) (meaning756 q) hs
  change valuationOf q 745 = false ∨ valuationOf q 756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 745 = false ∨ valuation q 756 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 745 = false ∨ valuationOf q 752 = false ∨ valuationOf q 757 = true := by
  have hs : count756 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (745)) (literal (valuationOf q) (752)) (literal (valuationOf q) (757)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -24, -25]) (count756 q) 1 1 (meaning745 q) (meaning752 q) (meaning757 q) hs
  change valuationOf q 745 = false ∨ valuationOf q 752 = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 745 = false ∨ valuation q 752 = false ∨ valuation q 757 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 745 = false ∨ valuationOf q 753 = false ∨ valuationOf q 758 = true := by
  have hs : count756 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (745)) (literal (valuationOf q) (753)) (literal (valuationOf q) (758)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -24, -25]) (count756 q) 1 2 (meaning745 q) (meaning753 q) (meaning758 q) hs
  change valuationOf q 745 = false ∨ valuationOf q 753 = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 745 = false ∨ valuation q 753 = false ∨ valuation q 758 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 745 = false ∨ valuationOf q 754 = false ∨ valuationOf q 759 = true := by
  have hs : count756 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (745)) (literal (valuationOf q) (754)) (literal (valuationOf q) (759)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -24, -25]) (count756 q) 1 3 (meaning745 q) (meaning754 q) (meaning759 q) hs
  change valuationOf q 745 = false ∨ valuationOf q 754 = false ∨ valuationOf q 759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 745 = false ∨ valuation q 754 = false ∨ valuation q 759 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E151.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112151
