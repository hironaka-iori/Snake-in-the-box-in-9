import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 34 = true ∨ valuationOf q 836 = true := by
  have hs : count835 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-34)) (literal (valuationOf q) (836)) (countLit q [-32]) (countLit q [-34]) (count835 q) 1 1 (meaningNeg32 q) (meaningNeg34 q) (meaning836 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 34)) = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 836 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 835 = false ∨ valuationOf q 837 = true := by
  have hs : count837 q = (countLit q [-31]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32, -34])
  have hm := merge_right (literal (valuationOf q) (835)) (literal (valuationOf q) (837)) (countLit q [-31]) (countLit q [-32, -34]) (count837 q) 1 (meaning835 q) (meaning837 q) hs
  change valuationOf q 835 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 835 = false ∨ valuation q 837 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 838 = true := by
  have hs : count837 q = (countLit q [-31]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32, -34])
  have hm := merge_right (literal (valuationOf q) (836)) (literal (valuationOf q) (838)) (countLit q [-31]) (countLit q [-32, -34]) (count837 q) 2 (meaning836 q) (meaning838 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 838 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 837 = true := by
  have hs : count837 q = (countLit q [-31]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32, -34])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (837)) (countLit q [-31]) (countLit q [-32, -34]) (count837 q) 1 (meaningNeg31 q) (meaning837 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 837 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 835 = false ∨ valuationOf q 838 = true := by
  have hs : count837 q = (countLit q [-31]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32, -34])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (835)) (literal (valuationOf q) (838)) (countLit q [-31]) (countLit q [-32, -34]) (count837 q) 1 1 (meaningNeg31 q) (meaning835 q) (meaning838 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 835 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 835 = false ∨ valuation q 838 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 840 = true := by
  have hs : count840 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (840)) (countLit q [-37]) (countLit q [-38]) (count840 q) 1 (meaningNeg38 q) (meaning840 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 840 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 840 = true := by
  have hs : count840 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (840)) (countLit q [-37]) (countLit q [-38]) (count840 q) 1 (meaningNeg37 q) (meaning840 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 840 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 38 = true ∨ valuationOf q 841 = true := by
  have hs : count840 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (841)) (countLit q [-37]) (countLit q [-38]) (count840 q) 1 1 (meaningNeg37 q) (meaningNeg38 q) (meaning841 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 841 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 842 = true := by
  have hs : count842 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (842)) (countLit q [-40]) (countLit q [-41]) (count842 q) 1 (meaningNeg41 q) (meaning842 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 842 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 842 = true := by
  have hs : count842 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (842)) (countLit q [-40]) (countLit q [-41]) (count842 q) 1 (meaningNeg40 q) (meaning842 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 842 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 41 = true ∨ valuationOf q 843 = true := by
  have hs : count842 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (843)) (countLit q [-40]) (countLit q [-41]) (count842 q) 1 1 (meaningNeg40 q) (meaningNeg41 q) (meaning843 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 41 = true ∨ valuation q 843 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 844 = true := by
  have hs : count844 q = (countLit q [-37, -38]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -41])
  have hm := merge_right (literal (valuationOf q) (842)) (literal (valuationOf q) (844)) (countLit q [-37, -38]) (countLit q [-40, -41]) (count844 q) 1 (meaning842 q) (meaning844 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 844 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 845 = true := by
  have hs : count844 q = (countLit q [-37, -38]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -41])
  have hm := merge_right (literal (valuationOf q) (843)) (literal (valuationOf q) (845)) (countLit q [-37, -38]) (countLit q [-40, -41]) (count844 q) 2 (meaning843 q) (meaning845 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 845 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 844 = true := by
  have hs : count844 q = (countLit q [-37, -38]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -41])
  have hm := merge_left (literal (valuationOf q) (840)) (literal (valuationOf q) (844)) (countLit q [-37, -38]) (countLit q [-40, -41]) (count844 q) 1 (meaning840 q) (meaning844 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 844 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 842 = false ∨ valuationOf q 845 = true := by
  have hs : count844 q = (countLit q [-37, -38]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -41])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (842)) (literal (valuationOf q) (845)) (countLit q [-37, -38]) (countLit q [-40, -41]) (count844 q) 1 1 (meaning840 q) (meaning842 q) (meaning845 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 842 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 842 = false ∨ valuation q 845 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 843 = false ∨ valuationOf q 846 = true := by
  have hs : count844 q = (countLit q [-37, -38]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -41])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (843)) (literal (valuationOf q) (846)) (countLit q [-37, -38]) (countLit q [-40, -41]) (count844 q) 1 2 (meaning840 q) (meaning843 q) (meaning846 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 843 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 843 = false ∨ valuation q 846 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 845 = true := by
  have hs : count844 q = (countLit q [-37, -38]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -41])
  have hm := merge_left (literal (valuationOf q) (841)) (literal (valuationOf q) (845)) (countLit q [-37, -38]) (countLit q [-40, -41]) (count844 q) 2 (meaning841 q) (meaning845 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 845 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 842 = false ∨ valuationOf q 846 = true := by
  have hs : count844 q = (countLit q [-37, -38]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -41])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (842)) (literal (valuationOf q) (846)) (countLit q [-37, -38]) (countLit q [-40, -41]) (count844 q) 2 1 (meaning841 q) (meaning842 q) (meaning846 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 842 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 842 = false ∨ valuation q 846 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 848 = true := by
  have hs : count848 q = (countLit q [-31, -32, -34]) + (countLit q [-37, -38, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34]) (l₂ := [-37, -38, -40, -41])
  have hm := merge_right (literal (valuationOf q) (844)) (literal (valuationOf q) (848)) (countLit q [-31, -32, -34]) (countLit q [-37, -38, -40, -41]) (count848 q) 1 (meaning844 q) (meaning848 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 848 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 849 = true := by
  have hs : count848 q = (countLit q [-31, -32, -34]) + (countLit q [-37, -38, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34]) (l₂ := [-37, -38, -40, -41])
  have hm := merge_right (literal (valuationOf q) (845)) (literal (valuationOf q) (849)) (countLit q [-31, -32, -34]) (countLit q [-37, -38, -40, -41]) (count848 q) 2 (meaning845 q) (meaning849 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 849 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 850 = true := by
  have hs : count848 q = (countLit q [-31, -32, -34]) + (countLit q [-37, -38, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34]) (l₂ := [-37, -38, -40, -41])
  have hm := merge_right (literal (valuationOf q) (846)) (literal (valuationOf q) (850)) (countLit q [-31, -32, -34]) (countLit q [-37, -38, -40, -41]) (count848 q) 3 (meaning846 q) (meaning850 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 850 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 848 = true := by
  have hs : count848 q = (countLit q [-31, -32, -34]) + (countLit q [-37, -38, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34]) (l₂ := [-37, -38, -40, -41])
  have hm := merge_left (literal (valuationOf q) (837)) (literal (valuationOf q) (848)) (countLit q [-31, -32, -34]) (countLit q [-37, -38, -40, -41]) (count848 q) 1 (meaning837 q) (meaning848 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 848 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 844 = false ∨ valuationOf q 849 = true := by
  have hs : count848 q = (countLit q [-31, -32, -34]) + (countLit q [-37, -38, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34]) (l₂ := [-37, -38, -40, -41])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (844)) (literal (valuationOf q) (849)) (countLit q [-31, -32, -34]) (countLit q [-37, -38, -40, -41]) (count848 q) 1 1 (meaning837 q) (meaning844 q) (meaning849 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 844 = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 844 = false ∨ valuation q 849 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 845 = false ∨ valuationOf q 850 = true := by
  have hs : count848 q = (countLit q [-31, -32, -34]) + (countLit q [-37, -38, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34]) (l₂ := [-37, -38, -40, -41])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (845)) (literal (valuationOf q) (850)) (countLit q [-31, -32, -34]) (countLit q [-37, -38, -40, -41]) (count848 q) 1 2 (meaning837 q) (meaning845 q) (meaning850 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 845 = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 845 = false ∨ valuation q 850 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 846 = false ∨ valuationOf q 851 = true := by
  have hs : count848 q = (countLit q [-31, -32, -34]) + (countLit q [-37, -38, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34]) (l₂ := [-37, -38, -40, -41])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (846)) (literal (valuationOf q) (851)) (countLit q [-31, -32, -34]) (countLit q [-37, -38, -40, -41]) (count848 q) 1 3 (meaning837 q) (meaning846 q) (meaning851 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 846 = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 846 = false ∨ valuation q 851 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 849 = true := by
  have hs : count848 q = (countLit q [-31, -32, -34]) + (countLit q [-37, -38, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34]) (l₂ := [-37, -38, -40, -41])
  have hm := merge_left (literal (valuationOf q) (838)) (literal (valuationOf q) (849)) (countLit q [-31, -32, -34]) (countLit q [-37, -38, -40, -41]) (count848 q) 2 (meaning838 q) (meaning849 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 849 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 844 = false ∨ valuationOf q 850 = true := by
  have hs : count848 q = (countLit q [-31, -32, -34]) + (countLit q [-37, -38, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34]) (l₂ := [-37, -38, -40, -41])
  have hm := merge_two (literal (valuationOf q) (838)) (literal (valuationOf q) (844)) (literal (valuationOf q) (850)) (countLit q [-31, -32, -34]) (countLit q [-37, -38, -40, -41]) (count848 q) 2 1 (meaning838 q) (meaning844 q) (meaning850 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 844 = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 844 = false ∨ valuation q 850 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 845 = false ∨ valuationOf q 851 = true := by
  have hs : count848 q = (countLit q [-31, -32, -34]) + (countLit q [-37, -38, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34]) (l₂ := [-37, -38, -40, -41])
  have hm := merge_two (literal (valuationOf q) (838)) (literal (valuationOf q) (845)) (literal (valuationOf q) (851)) (countLit q [-31, -32, -34]) (countLit q [-37, -38, -40, -41]) (count848 q) 2 2 (meaning838 q) (meaning845 q) (meaning851 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 845 = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 845 = false ∨ valuation q 851 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 855 = true := by
  have hs : count855 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (855)) (countLit q [-47]) (countLit q [-48]) (count855 q) 1 (meaningNeg48 q) (meaning855 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 855 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 855 = true := by
  have hs : count855 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (855)) (countLit q [-47]) (countLit q [-48]) (count855 q) 1 (meaningNeg47 q) (meaning855 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 855 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 48 = true ∨ valuationOf q 856 = true := by
  have hs : count855 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (856)) (countLit q [-47]) (countLit q [-48]) (count855 q) 1 1 (meaningNeg47 q) (meaningNeg48 q) (meaning856 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 48 = true ∨ valuation q 856 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 857 = true := by
  have hs : count857 q = (countLit q [-42]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-47, -48])
  have hm := merge_right (literal (valuationOf q) (855)) (literal (valuationOf q) (857)) (countLit q [-42]) (countLit q [-47, -48]) (count857 q) 1 (meaning855 q) (meaning857 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 857 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E051.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112051
