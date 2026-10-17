import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 90 = true ∨ valuationOf q 899 = true := by
  have hs : count898 q = (countLit q [-89]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (899)) (countLit q [-89]) (countLit q [-90]) (count898 q) 1 1 (meaningNeg89 q) (meaningNeg90 q) (meaning899 q) hs
  change (! (valuationOf q 89)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 90 = true ∨ valuation q 899 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 900 = true := by
  have hs : count900 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (900)) (countLit q [-92]) (countLit q [-93]) (count900 q) 1 (meaningNeg93 q) (meaning900 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 900 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 900 = true := by
  have hs : count900 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (900)) (countLit q [-92]) (countLit q [-93]) (count900 q) 1 (meaningNeg92 q) (meaning900 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 900 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 93 = true ∨ valuationOf q 901 = true := by
  have hs : count900 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (901)) (countLit q [-92]) (countLit q [-93]) (count900 q) 1 1 (meaningNeg92 q) (meaningNeg93 q) (meaning901 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 901 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 902 = true := by
  have hs : count902 q = (countLit q [-89, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (900)) (literal (valuationOf q) (902)) (countLit q [-89, -90]) (countLit q [-92, -93]) (count902 q) 1 (meaning900 q) (meaning902 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 902 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 903 = true := by
  have hs : count902 q = (countLit q [-89, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (901)) (literal (valuationOf q) (903)) (countLit q [-89, -90]) (countLit q [-92, -93]) (count902 q) 2 (meaning901 q) (meaning903 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 903 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 902 = true := by
  have hs : count902 q = (countLit q [-89, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (898)) (literal (valuationOf q) (902)) (countLit q [-89, -90]) (countLit q [-92, -93]) (count902 q) 1 (meaning898 q) (meaning902 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 902 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 900 = false ∨ valuationOf q 903 = true := by
  have hs : count902 q = (countLit q [-89, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (900)) (literal (valuationOf q) (903)) (countLit q [-89, -90]) (countLit q [-92, -93]) (count902 q) 1 1 (meaning898 q) (meaning900 q) (meaning903 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 900 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 900 = false ∨ valuation q 903 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 901 = false ∨ valuationOf q 904 = true := by
  have hs : count902 q = (countLit q [-89, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (901)) (literal (valuationOf q) (904)) (countLit q [-89, -90]) (countLit q [-92, -93]) (count902 q) 1 2 (meaning898 q) (meaning901 q) (meaning904 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 901 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 901 = false ∨ valuation q 904 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 903 = true := by
  have hs : count902 q = (countLit q [-89, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (899)) (literal (valuationOf q) (903)) (countLit q [-89, -90]) (countLit q [-92, -93]) (count902 q) 2 (meaning899 q) (meaning903 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 903 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 900 = false ∨ valuationOf q 904 = true := by
  have hs : count902 q = (countLit q [-89, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (900)) (literal (valuationOf q) (904)) (countLit q [-89, -90]) (countLit q [-92, -93]) (count902 q) 2 1 (meaning899 q) (meaning900 q) (meaning904 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 900 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 900 = false ∨ valuation q 904 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 906 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_right (literal (valuationOf q) (902)) (literal (valuationOf q) (906)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 1 (meaning902 q) (meaning906 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 906 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 903 = false ∨ valuationOf q 907 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_right (literal (valuationOf q) (903)) (literal (valuationOf q) (907)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 2 (meaning903 q) (meaning907 q) hs
  change valuationOf q 903 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 903 = false ∨ valuation q 907 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 904 = false ∨ valuationOf q 908 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_right (literal (valuationOf q) (904)) (literal (valuationOf q) (908)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 3 (meaning904 q) (meaning908 q) hs
  change valuationOf q 904 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 904 = false ∨ valuation q 908 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 906 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_left (literal (valuationOf q) (895)) (literal (valuationOf q) (906)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 1 (meaning895 q) (meaning906 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 906 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 902 = false ∨ valuationOf q 907 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (902)) (literal (valuationOf q) (907)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 1 1 (meaning895 q) (meaning902 q) (meaning907 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 902 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 902 = false ∨ valuation q 907 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 903 = false ∨ valuationOf q 908 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (903)) (literal (valuationOf q) (908)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 1 2 (meaning895 q) (meaning903 q) (meaning908 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 903 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 903 = false ∨ valuation q 908 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 904 = false ∨ valuationOf q 909 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (904)) (literal (valuationOf q) (909)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 1 3 (meaning895 q) (meaning904 q) (meaning909 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 904 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 904 = false ∨ valuation q 909 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 907 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_left (literal (valuationOf q) (896)) (literal (valuationOf q) (907)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 2 (meaning896 q) (meaning907 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 907 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 902 = false ∨ valuationOf q 908 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (902)) (literal (valuationOf q) (908)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 2 1 (meaning896 q) (meaning902 q) (meaning908 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 902 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 902 = false ∨ valuation q 908 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 903 = false ∨ valuationOf q 909 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (903)) (literal (valuationOf q) (909)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 2 2 (meaning896 q) (meaning903 q) (meaning909 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 903 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 903 = false ∨ valuation q 909 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 904 = false ∨ valuationOf q 910 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (904)) (literal (valuationOf q) (910)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 2 3 (meaning896 q) (meaning904 q) (meaning910 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 904 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 904 = false ∨ valuation q 910 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 908 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_left (literal (valuationOf q) (897)) (literal (valuationOf q) (908)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 3 (meaning897 q) (meaning908 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 908 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 902 = false ∨ valuationOf q 909 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (902)) (literal (valuationOf q) (909)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 3 1 (meaning897 q) (meaning902 q) (meaning909 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 902 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 902 = false ∨ valuation q 909 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 903 = false ∨ valuationOf q 910 = true := by
  have hs : count906 q = (countLit q [-80, -83, -87]) + (countLit q [-89, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87]) (l₂ := [-89, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (903)) (literal (valuationOf q) (910)) (countLit q [-80, -83, -87]) (countLit q [-89, -90, -92, -93]) (count906 q) 3 2 (meaning897 q) (meaning903 q) (meaning910 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 903 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 903 = false ∨ valuation q 910 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 913 = true := by
  have hs : count913 q = (countLit q [-97]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (913)) (countLit q [-97]) (countLit q [-98]) (count913 q) 1 (meaningNeg98 q) (meaning913 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 913 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 98 = true ∨ valuationOf q 914 = true := by
  have hs : count913 q = (countLit q [-97]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (914)) (countLit q [-97]) (countLit q [-98]) (count913 q) 1 1 (meaningNeg97 q) (meaningNeg98 q) (meaning914 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 914 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 913 = false ∨ valuationOf q 916 = true := by
  have hs : count915 q = (countLit q [-96]) + (countLit q [-97, -98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97, -98])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (913)) (literal (valuationOf q) (916)) (countLit q [-96]) (countLit q [-97, -98]) (count915 q) 1 1 (meaningNeg96 q) (meaning913 q) (meaning916 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 913 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 913 = false ∨ valuation q 916 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 914 = false ∨ valuationOf q 917 = true := by
  have hs : count915 q = (countLit q [-96]) + (countLit q [-97, -98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97, -98])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (914)) (literal (valuationOf q) (917)) (countLit q [-96]) (countLit q [-97, -98]) (count915 q) 1 2 (meaningNeg96 q) (meaning914 q) (meaning917 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 914 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 914 = false ∨ valuation q 917 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 918 = true := by
  have hs : count918 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (918)) (countLit q [-100]) (countLit q [-101]) (count918 q) 1 (meaningNeg101 q) (meaning918 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 918 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 918 = true := by
  have hs : count918 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (918)) (countLit q [-100]) (countLit q [-101]) (count918 q) 1 (meaningNeg100 q) (meaning918 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 918 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 101 = true ∨ valuationOf q 919 = true := by
  have hs : count918 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-100)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (919)) (countLit q [-100]) (countLit q [-101]) (count918 q) 1 1 (meaningNeg100 q) (meaningNeg101 q) (meaning919 q) hs
  change (! (valuationOf q 100)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 919 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E151.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112151
