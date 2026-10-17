import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 744 = false ∨ valuationOf q 747 = true := by
  have hs : count747 q = (countLit q [-28, -29, -30]) + (countLit q [-33, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30]) (l₂ := [-33, -37, -39])
  have hm := merge_right (literal (valuationOf q) (744)) (literal (valuationOf q) (747)) (countLit q [-28, -29, -30]) (countLit q [-33, -37, -39]) (count747 q) 1 (meaning744 q) (meaning747 q) hs
  change valuationOf q 744 = false ∨ valuationOf q 747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 744 = false ∨ valuation q 747 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 745 = false ∨ valuationOf q 748 = true := by
  have hs : count747 q = (countLit q [-28, -29, -30]) + (countLit q [-33, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30]) (l₂ := [-33, -37, -39])
  have hm := merge_right (literal (valuationOf q) (745)) (literal (valuationOf q) (748)) (countLit q [-28, -29, -30]) (countLit q [-33, -37, -39]) (count747 q) 2 (meaning745 q) (meaning748 q) hs
  change valuationOf q 745 = false ∨ valuationOf q 748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 745 = false ∨ valuation q 748 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 739 = false ∨ valuationOf q 744 = false ∨ valuationOf q 748 = true := by
  have hs : count747 q = (countLit q [-28, -29, -30]) + (countLit q [-33, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30]) (l₂ := [-33, -37, -39])
  have hm := merge_two (literal (valuationOf q) (739)) (literal (valuationOf q) (744)) (literal (valuationOf q) (748)) (countLit q [-28, -29, -30]) (countLit q [-33, -37, -39]) (count747 q) 1 1 (meaning739 q) (meaning744 q) (meaning748 q) hs
  change valuationOf q 739 = false ∨ valuationOf q 744 = false ∨ valuationOf q 748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 739 = false ∨ valuation q 744 = false ∨ valuation q 748 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 739 = false ∨ valuationOf q 745 = false ∨ valuationOf q 749 = true := by
  have hs : count747 q = (countLit q [-28, -29, -30]) + (countLit q [-33, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30]) (l₂ := [-33, -37, -39])
  have hm := merge_two (literal (valuationOf q) (739)) (literal (valuationOf q) (745)) (literal (valuationOf q) (749)) (countLit q [-28, -29, -30]) (countLit q [-33, -37, -39]) (count747 q) 1 2 (meaning739 q) (meaning745 q) (meaning749 q) hs
  change valuationOf q 739 = false ∨ valuationOf q 745 = false ∨ valuationOf q 749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 739 = false ∨ valuation q 745 = false ∨ valuation q 749 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 753 = true := by
  have hs : count753 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (753)) (countLit q [-43]) (countLit q [-44]) (count753 q) 1 (meaningNeg44 q) (meaning753 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 753 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 753 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 753 = true := by
  have hs : count753 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (753)) (countLit q [-43]) (countLit q [-44]) (count753 q) 1 (meaningNeg43 q) (meaning753 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 753 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 753 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 44 = true ∨ valuationOf q 754 = true := by
  have hs : count753 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (754)) (countLit q [-43]) (countLit q [-44]) (count753 q) 1 1 (meaningNeg43 q) (meaningNeg44 q) (meaning754 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 754 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 754 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 753 = false ∨ valuationOf q 755 = true := by
  have hs : count755 q = (countLit q [-40]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -44])
  have hm := merge_right (literal (valuationOf q) (753)) (literal (valuationOf q) (755)) (countLit q [-40]) (countLit q [-43, -44]) (count755 q) 1 (meaning753 q) (meaning755 q) hs
  change valuationOf q 753 = false ∨ valuationOf q 755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 753 = false ∨ valuation q 755 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 755 = true := by
  have hs : count755 q = (countLit q [-40]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (755)) (countLit q [-40]) (countLit q [-43, -44]) (count755 q) 1 (meaningNeg40 q) (meaning755 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 755 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 755 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 753 = false ∨ valuationOf q 756 = true := by
  have hs : count755 q = (countLit q [-40]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (753)) (literal (valuationOf q) (756)) (countLit q [-40]) (countLit q [-43, -44]) (count755 q) 1 1 (meaningNeg40 q) (meaning753 q) (meaning756 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 753 = false ∨ valuationOf q 756 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 753 = false ∨ valuation q 756 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 754 = false ∨ valuationOf q 757 = true := by
  have hs : count755 q = (countLit q [-40]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (754)) (literal (valuationOf q) (757)) (countLit q [-40]) (countLit q [-43, -44]) (count755 q) 1 2 (meaningNeg40 q) (meaning754 q) (meaning757 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 754 = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 754 = false ∨ valuation q 757 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 758 = true := by
  have hs : count758 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (758)) (countLit q [-45]) (countLit q [-47]) (count758 q) 1 (meaningNeg47 q) (meaning758 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 758 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 758 = true := by
  have hs : count758 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (758)) (countLit q [-45]) (countLit q [-47]) (count758 q) 1 (meaningNeg45 q) (meaning758 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 758 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 47 = true ∨ valuationOf q 759 = true := by
  have hs : count758 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (759)) (countLit q [-45]) (countLit q [-47]) (count758 q) 1 1 (meaningNeg45 q) (meaningNeg47 q) (meaning759 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 759 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 47 = true ∨ valuation q 759 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 760 = true := by
  have hs : count760 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (760)) (countLit q [-50]) (countLit q [-52]) (count760 q) 1 (meaningNeg52 q) (meaning760 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 760 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 760 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 760 = true := by
  have hs : count760 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (760)) (countLit q [-50]) (countLit q [-52]) (count760 q) 1 (meaningNeg50 q) (meaning760 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 760 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 760 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 760 = false ∨ valuationOf q 762 = true := by
  have hs : count762 q = (countLit q [-45, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-50, -52])
  have hm := merge_right (literal (valuationOf q) (760)) (literal (valuationOf q) (762)) (countLit q [-45, -47]) (countLit q [-50, -52]) (count762 q) 1 (meaning760 q) (meaning762 q) hs
  change valuationOf q 760 = false ∨ valuationOf q 762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 760 = false ∨ valuation q 762 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 762 = true := by
  have hs : count762 q = (countLit q [-45, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-50, -52])
  have hm := merge_left (literal (valuationOf q) (758)) (literal (valuationOf q) (762)) (countLit q [-45, -47]) (countLit q [-50, -52]) (count762 q) 1 (meaning758 q) (meaning762 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 762 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 760 = false ∨ valuationOf q 763 = true := by
  have hs : count762 q = (countLit q [-45, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-50, -52])
  have hm := merge_two (literal (valuationOf q) (758)) (literal (valuationOf q) (760)) (literal (valuationOf q) (763)) (countLit q [-45, -47]) (countLit q [-50, -52]) (count762 q) 1 1 (meaning758 q) (meaning760 q) (meaning763 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 760 = false ∨ valuationOf q 763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 760 = false ∨ valuation q 763 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 759 = false ∨ valuationOf q 763 = true := by
  have hs : count762 q = (countLit q [-45, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-50, -52])
  have hm := merge_left (literal (valuationOf q) (759)) (literal (valuationOf q) (763)) (countLit q [-45, -47]) (countLit q [-50, -52]) (count762 q) 2 (meaning759 q) (meaning763 q) hs
  change valuationOf q 759 = false ∨ valuationOf q 763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 759 = false ∨ valuation q 763 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 755 = false ∨ valuationOf q 766 = true := by
  have hs : count766 q = (countLit q [-40, -43, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_left (literal (valuationOf q) (755)) (literal (valuationOf q) (766)) (countLit q [-40, -43, -44]) (countLit q [-45, -47, -50, -52]) (count766 q) 1 (meaning755 q) (meaning766 q) hs
  change valuationOf q 755 = false ∨ valuationOf q 766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 755 = false ∨ valuation q 766 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 755 = false ∨ valuationOf q 762 = false ∨ valuationOf q 767 = true := by
  have hs : count766 q = (countLit q [-40, -43, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (755)) (literal (valuationOf q) (762)) (literal (valuationOf q) (767)) (countLit q [-40, -43, -44]) (countLit q [-45, -47, -50, -52]) (count766 q) 1 1 (meaning755 q) (meaning762 q) (meaning767 q) hs
  change valuationOf q 755 = false ∨ valuationOf q 762 = false ∨ valuationOf q 767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 755 = false ∨ valuation q 762 = false ∨ valuation q 767 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 755 = false ∨ valuationOf q 763 = false ∨ valuationOf q 768 = true := by
  have hs : count766 q = (countLit q [-40, -43, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (755)) (literal (valuationOf q) (763)) (literal (valuationOf q) (768)) (countLit q [-40, -43, -44]) (countLit q [-45, -47, -50, -52]) (count766 q) 1 2 (meaning755 q) (meaning763 q) (meaning768 q) hs
  change valuationOf q 755 = false ∨ valuationOf q 763 = false ∨ valuationOf q 768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 755 = false ∨ valuation q 763 = false ∨ valuation q 768 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 756 = false ∨ valuationOf q 767 = true := by
  have hs : count766 q = (countLit q [-40, -43, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_left (literal (valuationOf q) (756)) (literal (valuationOf q) (767)) (countLit q [-40, -43, -44]) (countLit q [-45, -47, -50, -52]) (count766 q) 2 (meaning756 q) (meaning767 q) hs
  change valuationOf q 756 = false ∨ valuationOf q 767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 756 = false ∨ valuation q 767 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 756 = false ∨ valuationOf q 762 = false ∨ valuationOf q 768 = true := by
  have hs : count766 q = (countLit q [-40, -43, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (756)) (literal (valuationOf q) (762)) (literal (valuationOf q) (768)) (countLit q [-40, -43, -44]) (countLit q [-45, -47, -50, -52]) (count766 q) 2 1 (meaning756 q) (meaning762 q) (meaning768 q) hs
  change valuationOf q 756 = false ∨ valuationOf q 762 = false ∨ valuationOf q 768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 756 = false ∨ valuation q 762 = false ∨ valuation q 768 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 757 = false ∨ valuationOf q 768 = true := by
  have hs : count766 q = (countLit q [-40, -43, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_left (literal (valuationOf q) (757)) (literal (valuationOf q) (768)) (countLit q [-40, -43, -44]) (countLit q [-45, -47, -50, -52]) (count766 q) 3 (meaning757 q) (meaning768 q) hs
  change valuationOf q 757 = false ∨ valuationOf q 768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 757 = false ∨ valuation q 768 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 766 = false ∨ valuationOf q 773 = true := by
  have hs : count773 q = (countLit q [-28, -29, -30, -33, -37, -39]) + (countLit q [-40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -37, -39]) (l₂ := [-40, -43, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (766)) (literal (valuationOf q) (773)) (countLit q [-28, -29, -30, -33, -37, -39]) (countLit q [-40, -43, -44, -45, -47, -50, -52]) (count773 q) 1 (meaning766 q) (meaning773 q) hs
  change valuationOf q 766 = false ∨ valuationOf q 773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 766 = false ∨ valuation q 773 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 767 = false ∨ valuationOf q 774 = true := by
  have hs : count773 q = (countLit q [-28, -29, -30, -33, -37, -39]) + (countLit q [-40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -37, -39]) (l₂ := [-40, -43, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (767)) (literal (valuationOf q) (774)) (countLit q [-28, -29, -30, -33, -37, -39]) (countLit q [-40, -43, -44, -45, -47, -50, -52]) (count773 q) 2 (meaning767 q) (meaning774 q) hs
  change valuationOf q 767 = false ∨ valuationOf q 774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 767 = false ∨ valuation q 774 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 768 = false ∨ valuationOf q 775 = true := by
  have hs : count773 q = (countLit q [-28, -29, -30, -33, -37, -39]) + (countLit q [-40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -37, -39]) (l₂ := [-40, -43, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (768)) (literal (valuationOf q) (775)) (countLit q [-28, -29, -30, -33, -37, -39]) (countLit q [-40, -43, -44, -45, -47, -50, -52]) (count773 q) 3 (meaning768 q) (meaning775 q) hs
  change valuationOf q 768 = false ∨ valuationOf q 775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 768 = false ∨ valuation q 775 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 747 = false ∨ valuationOf q 766 = false ∨ valuationOf q 774 = true := by
  have hs : count773 q = (countLit q [-28, -29, -30, -33, -37, -39]) + (countLit q [-40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -37, -39]) (l₂ := [-40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (747)) (literal (valuationOf q) (766)) (literal (valuationOf q) (774)) (countLit q [-28, -29, -30, -33, -37, -39]) (countLit q [-40, -43, -44, -45, -47, -50, -52]) (count773 q) 1 1 (meaning747 q) (meaning766 q) (meaning774 q) hs
  change valuationOf q 747 = false ∨ valuationOf q 766 = false ∨ valuationOf q 774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 747 = false ∨ valuation q 766 = false ∨ valuation q 774 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 747 = false ∨ valuationOf q 767 = false ∨ valuationOf q 775 = true := by
  have hs : count773 q = (countLit q [-28, -29, -30, -33, -37, -39]) + (countLit q [-40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -37, -39]) (l₂ := [-40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (747)) (literal (valuationOf q) (767)) (literal (valuationOf q) (775)) (countLit q [-28, -29, -30, -33, -37, -39]) (countLit q [-40, -43, -44, -45, -47, -50, -52]) (count773 q) 1 2 (meaning747 q) (meaning767 q) (meaning775 q) hs
  change valuationOf q 747 = false ∨ valuationOf q 767 = false ∨ valuationOf q 775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 747 = false ∨ valuation q 767 = false ∨ valuation q 775 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 747 = false ∨ valuationOf q 768 = false ∨ valuationOf q 776 = true := by
  have hs : count773 q = (countLit q [-28, -29, -30, -33, -37, -39]) + (countLit q [-40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -37, -39]) (l₂ := [-40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (747)) (literal (valuationOf q) (768)) (literal (valuationOf q) (776)) (countLit q [-28, -29, -30, -33, -37, -39]) (countLit q [-40, -43, -44, -45, -47, -50, -52]) (count773 q) 1 3 (meaning747 q) (meaning768 q) (meaning776 q) hs
  change valuationOf q 747 = false ∨ valuationOf q 768 = false ∨ valuationOf q 776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 747 = false ∨ valuation q 768 = false ∨ valuation q 776 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E075.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112075
