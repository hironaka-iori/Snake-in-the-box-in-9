import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 825 = true := by
  have hs : count825 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (825)) (countLit q [-61]) (countLit q [-62]) (count825 q) 1 (meaningNeg62 q) (meaning825 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 825 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 827 = true := by
  have hs : count827 q = (countLit q [-60]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -62])
  have hm := merge_right (literal (valuationOf q) (825)) (literal (valuationOf q) (827)) (countLit q [-60]) (countLit q [-61, -62]) (count827 q) 1 (meaning825 q) (meaning827 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 827 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 827 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-52, -54, -56]) + (countLit q [-60, -61, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -56]) (l₂ := [-60, -61, -62])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (827)) (literal (valuationOf q) (831)) (countLit q [-52, -54, -56]) (countLit q [-60, -61, -62]) (count830 q) 1 1 (meaning822 q) (meaning827 q) (meaning831 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 827 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 827 = false ∨ valuation q 831 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 836 = true := by
  have hs : count836 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (836)) (countLit q [-66]) (countLit q [-68]) (count836 q) 1 (meaningNeg68 q) (meaning836 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 836 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 838 = true := by
  have hs : count838 q = (countLit q [-64]) + (countLit q [-66, -68]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -68])
  have hm := merge_right (literal (valuationOf q) (836)) (literal (valuationOf q) (838)) (countLit q [-64]) (countLit q [-66, -68]) (count838 q) 1 (meaning836 q) (meaning838 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 838 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 841 = true := by
  have hs : count841 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (841)) (countLit q [-70]) (countLit q [-72]) (count841 q) 1 (meaningNeg72 q) (meaning841 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 841 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 845 = true := by
  have hs : count845 q = (countLit q [-70, -72]) + (countLit q [-73, -75]) := List.countP_append (p := literal q) (l₁ := [-70, -72]) (l₂ := [-73, -75])
  have hm := merge_left (literal (valuationOf q) (841)) (literal (valuationOf q) (845)) (countLit q [-70, -72]) (countLit q [-73, -75]) (count845 q) 1 (meaning841 q) (meaning845 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 845 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 845 = false ∨ valuationOf q 850 = true := by
  have hs : count849 q = (countLit q [-64, -66, -68]) + (countLit q [-70, -72, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-70, -72, -73, -75])
  have hm := merge_two (literal (valuationOf q) (838)) (literal (valuationOf q) (845)) (literal (valuationOf q) (850)) (countLit q [-64, -66, -68]) (countLit q [-70, -72, -73, -75]) (count849 q) 1 1 (meaning838 q) (meaning845 q) (meaning850 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 845 = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 845 = false ∨ valuation q 850 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 831 = false ∨ valuationOf q 850 = false ∨ valuationOf q 859 = true := by
  have hs : count856 q = (countLit q [-52, -54, -56, -60, -61, -62]) + (countLit q [-64, -66, -68, -70, -72, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -56, -60, -61, -62]) (l₂ := [-64, -66, -68, -70, -72, -73, -75])
  have hm := merge_two (literal (valuationOf q) (831)) (literal (valuationOf q) (850)) (literal (valuationOf q) (859)) (countLit q [-52, -54, -56, -60, -61, -62]) (countLit q [-64, -66, -68, -70, -72, -73, -75]) (count856 q) 2 2 (meaning831 q) (meaning850 q) (meaning859 q) hs
  change valuationOf q 831 = false ∨ valuationOf q 850 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 831 = false ∨ valuation q 850 = false ∨ valuation q 859 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 925 = true := by
  have hs : count922 q = (countLit q [-52, -54, -56, -60, -61, -62, -64, -66, -68, -70, -72, -73, -75]) + (countLit q [-78, -80, -81, -82, -87, -88, -89, -91, -94, -96, -97, -98, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -56, -60, -61, -62, -64, -66, -68, -70, -72, -73, -75]) (l₂ := [-78, -80, -81, -82, -87, -88, -89, -91, -94, -96, -97, -98, -103, -104])
  have hm := merge_left (literal (valuationOf q) (859)) (literal (valuationOf q) (925)) (countLit q [-52, -54, -56, -60, -61, -62, -64, -66, -68, -70, -72, -73, -75]) (countLit q [-78, -80, -81, -82, -87, -88, -89, -91, -94, -96, -97, -98, -103, -104]) (count922 q) 4 (meaning859 q) (meaning925 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 925 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 925 = false ∨ valuationOf q 947 = true := by
  have hs : count935 q = (countLit q [-1, -3, -4, -5, -9, -10, -12, -15, -17, -19, -20, -22, -26, -27, -28, -33, -34, -36, -37, -39, -40, -44, -46, -48, -49, -51]) + (countLit q [-52, -54, -56, -60, -61, -62, -64, -66, -68, -70, -72, -73, -75, -78, -80, -81, -82, -87, -88, -89, -91, -94, -96, -97, -98, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -12, -15, -17, -19, -20, -22, -26, -27, -28, -33, -34, -36, -37, -39, -40, -44, -46, -48, -49, -51]) (l₂ := [-52, -54, -56, -60, -61, -62, -64, -66, -68, -70, -72, -73, -75, -78, -80, -81, -82, -87, -88, -89, -91, -94, -96, -97, -98, -103, -104])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (925)) (literal (valuationOf q) (947)) (countLit q [-1, -3, -4, -5, -9, -10, -12, -15, -17, -19, -20, -22, -26, -27, -28, -33, -34, -36, -37, -39, -40, -44, -46, -48, -49, -51]) (countLit q [-52, -54, -56, -60, -61, -62, -64, -66, -68, -70, -72, -73, -75, -78, -80, -81, -82, -87, -88, -89, -91, -94, -96, -97, -98, -103, -104]) (count935 q) 9 4 (meaning815 q) (meaning925 q) (meaning947 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 925 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 925 = false ∨ valuation q 947 = true := counterClause459 (baseVal q)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 947 = false := by
  rw [value947]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count935 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause461 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1232 = true := by
  have hs : count1232 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1232)) (countLit q [-6]) (countLit q [-7]) (count1232 q) 1 (meaningNeg7 q) (meaning1232 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1232 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1232 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1232 = true := by
  have hs : count1232 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1232)) (countLit q [-6]) (countLit q [-7]) (count1232 q) 1 (meaningNeg6 q) (meaning1232 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1232 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1232 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1233 = true := by
  have hs : count1232 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1233)) (countLit q [-6]) (countLit q [-7]) (count1232 q) 1 1 (meaningNeg6 q) (meaningNeg7 q) (meaning1233 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 1233 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 1232 = false ∨ valuationOf q 1234 = true := by
  have hs : count1234 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (1232)) (literal (valuationOf q) (1234)) (countLit q [-2]) (countLit q [-6, -7]) (count1234 q) 1 (meaning1232 q) (meaning1234 q) hs
  change valuationOf q 1232 = false ∨ valuationOf q 1234 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 1232 = false ∨ valuation q 1234 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1235 = true := by
  have hs : count1234 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (1233)) (literal (valuationOf q) (1235)) (countLit q [-2]) (countLit q [-6, -7]) (count1234 q) 2 (meaning1233 q) (meaning1235 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1235 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1234 = true := by
  have hs : count1234 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1234)) (countLit q [-2]) (countLit q [-6, -7]) (count1234 q) 1 (meaningNeg2 q) (meaning1234 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1234 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1234 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1232 = false ∨ valuationOf q 1235 = true := by
  have hs : count1234 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1232)) (literal (valuationOf q) (1235)) (countLit q [-2]) (countLit q [-6, -7]) (count1234 q) 1 1 (meaningNeg2 q) (meaning1232 q) (meaning1235 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1232 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1232 = false ∨ valuation q 1235 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1233 = false ∨ valuationOf q 1236 = true := by
  have hs : count1234 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1233)) (literal (valuationOf q) (1236)) (countLit q [-2]) (countLit q [-6, -7]) (count1234 q) 1 2 (meaningNeg2 q) (meaning1233 q) (meaning1236 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1233 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1233 = false ∨ valuation q 1236 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1237 = true := by
  have hs : count1237 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1237)) (countLit q [-11]) (countLit q [-13]) (count1237 q) 1 (meaningNeg13 q) (meaning1237 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1237 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1237 = true := by
  have hs : count1237 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1237)) (countLit q [-11]) (countLit q [-13]) (count1237 q) 1 (meaningNeg11 q) (meaning1237 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1237 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1238 = true := by
  have hs : count1237 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1238)) (countLit q [-11]) (countLit q [-13]) (count1237 q) 1 1 (meaningNeg11 q) (meaningNeg13 q) (meaning1238 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1238 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 13 = true ∨ valuation q 1238 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 1237 = false ∨ valuationOf q 1239 = true := by
  have hs : count1239 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_right (literal (valuationOf q) (1237)) (literal (valuationOf q) (1239)) (countLit q [-8]) (countLit q [-11, -13]) (count1239 q) 1 (meaning1237 q) (meaning1239 q) hs
  change valuationOf q 1237 = false ∨ valuationOf q 1239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 1237 = false ∨ valuation q 1239 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 1238 = false ∨ valuationOf q 1240 = true := by
  have hs : count1239 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_right (literal (valuationOf q) (1238)) (literal (valuationOf q) (1240)) (countLit q [-8]) (countLit q [-11, -13]) (count1239 q) 2 (meaning1238 q) (meaning1240 q) hs
  change valuationOf q 1238 = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 1238 = false ∨ valuation q 1240 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1239 = true := by
  have hs : count1239 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1239)) (countLit q [-8]) (countLit q [-11, -13]) (count1239 q) 1 (meaningNeg8 q) (meaning1239 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1239 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1239 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1237 = false ∨ valuationOf q 1240 = true := by
  have hs : count1239 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1237)) (literal (valuationOf q) (1240)) (countLit q [-8]) (countLit q [-11, -13]) (count1239 q) 1 1 (meaningNeg8 q) (meaning1237 q) (meaning1240 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1237 = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1237 = false ∨ valuation q 1240 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1238 = false ∨ valuationOf q 1241 = true := by
  have hs : count1239 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1238)) (literal (valuationOf q) (1241)) (countLit q [-8]) (countLit q [-11, -13]) (count1239 q) 1 2 (meaningNeg8 q) (meaning1238 q) (meaning1241 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1238 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1238 = false ∨ valuation q 1241 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 1239 = false ∨ valuationOf q 1242 = true := by
  have hs : count1242 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_right (literal (valuationOf q) (1239)) (literal (valuationOf q) (1242)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1242 q) 1 (meaning1239 q) (meaning1242 q) hs
  change valuationOf q 1239 = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 1239 = false ∨ valuation q 1242 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1240 = false ∨ valuationOf q 1243 = true := by
  have hs : count1242 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_right (literal (valuationOf q) (1240)) (literal (valuationOf q) (1243)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1242 q) 2 (meaning1240 q) (meaning1243 q) hs
  change valuationOf q 1240 = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1240 = false ∨ valuation q 1243 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1244 = true := by
  have hs : count1242 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_right (literal (valuationOf q) (1241)) (literal (valuationOf q) (1244)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1242 q) 3 (meaning1241 q) (meaning1244 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1244 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 1234 = false ∨ valuationOf q 1242 = true := by
  have hs : count1242 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_left (literal (valuationOf q) (1234)) (literal (valuationOf q) (1242)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1242 q) 1 (meaning1234 q) (meaning1242 q) hs
  change valuationOf q 1234 = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 1234 = false ∨ valuation q 1242 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E145.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112145
