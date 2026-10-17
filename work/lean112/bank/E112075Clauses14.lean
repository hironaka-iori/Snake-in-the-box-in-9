import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 835 = true := by
  have hs : count835 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (835)) (countLit q [-82]) (countLit q [-84]) (count835 q) 1 (meaningNeg82 q) (meaning835 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 835 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 84 = true ∨ valuationOf q 836 = true := by
  have hs : count835 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (836)) (countLit q [-82]) (countLit q [-84]) (count835 q) 1 1 (meaningNeg82 q) (meaningNeg84 q) (meaning836 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 836 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 835 = false ∨ valuationOf q 837 = true := by
  have hs : count837 q = (countLit q [-80]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82, -84])
  have hm := merge_right (literal (valuationOf q) (835)) (literal (valuationOf q) (837)) (countLit q [-80]) (countLit q [-82, -84]) (count837 q) 1 (meaning835 q) (meaning837 q) hs
  change valuationOf q 835 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 835 = false ∨ valuation q 837 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 838 = true := by
  have hs : count837 q = (countLit q [-80]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82, -84])
  have hm := merge_right (literal (valuationOf q) (836)) (literal (valuationOf q) (838)) (countLit q [-80]) (countLit q [-82, -84]) (count837 q) 2 (meaning836 q) (meaning838 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 838 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 837 = true := by
  have hs : count837 q = (countLit q [-80]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82, -84])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (837)) (countLit q [-80]) (countLit q [-82, -84]) (count837 q) 1 (meaningNeg80 q) (meaning837 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 837 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 835 = false ∨ valuationOf q 838 = true := by
  have hs : count837 q = (countLit q [-80]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82, -84])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (835)) (literal (valuationOf q) (838)) (countLit q [-80]) (countLit q [-82, -84]) (count837 q) 1 1 (meaningNeg80 q) (meaning835 q) (meaning838 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 835 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 835 = false ∨ valuation q 838 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 840 = true := by
  have hs : count840 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (840)) (countLit q [-87]) (countLit q [-90]) (count840 q) 1 (meaningNeg90 q) (meaning840 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 840 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 840 = true := by
  have hs : count840 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (840)) (countLit q [-87]) (countLit q [-90]) (count840 q) 1 (meaningNeg87 q) (meaning840 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 840 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 90 = true ∨ valuationOf q 841 = true := by
  have hs : count840 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (841)) (countLit q [-87]) (countLit q [-90]) (count840 q) 1 1 (meaningNeg87 q) (meaningNeg90 q) (meaning841 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 90 = true ∨ valuation q 841 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 842 = true := by
  have hs : count842 q = (countLit q [-86]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87, -90])
  have hm := merge_right (literal (valuationOf q) (840)) (literal (valuationOf q) (842)) (countLit q [-86]) (countLit q [-87, -90]) (count842 q) 1 (meaning840 q) (meaning842 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 842 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 843 = true := by
  have hs : count842 q = (countLit q [-86]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87, -90])
  have hm := merge_right (literal (valuationOf q) (841)) (literal (valuationOf q) (843)) (countLit q [-86]) (countLit q [-87, -90]) (count842 q) 2 (meaning841 q) (meaning843 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 843 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 842 = true := by
  have hs : count842 q = (countLit q [-86]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87, -90])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (842)) (countLit q [-86]) (countLit q [-87, -90]) (count842 q) 1 (meaningNeg86 q) (meaning842 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 842 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 840 = false ∨ valuationOf q 843 = true := by
  have hs : count842 q = (countLit q [-86]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87, -90])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (840)) (literal (valuationOf q) (843)) (countLit q [-86]) (countLit q [-87, -90]) (count842 q) 1 1 (meaningNeg86 q) (meaning840 q) (meaning843 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 840 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 840 = false ∨ valuation q 843 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 845 = true := by
  have hs : count845 q = (countLit q [-80, -82, -84]) + (countLit q [-86, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84]) (l₂ := [-86, -87, -90])
  have hm := merge_right (literal (valuationOf q) (842)) (literal (valuationOf q) (845)) (countLit q [-80, -82, -84]) (countLit q [-86, -87, -90]) (count845 q) 1 (meaning842 q) (meaning845 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 845 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 846 = true := by
  have hs : count845 q = (countLit q [-80, -82, -84]) + (countLit q [-86, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84]) (l₂ := [-86, -87, -90])
  have hm := merge_right (literal (valuationOf q) (843)) (literal (valuationOf q) (846)) (countLit q [-80, -82, -84]) (countLit q [-86, -87, -90]) (count845 q) 2 (meaning843 q) (meaning846 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 846 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 845 = true := by
  have hs : count845 q = (countLit q [-80, -82, -84]) + (countLit q [-86, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84]) (l₂ := [-86, -87, -90])
  have hm := merge_left (literal (valuationOf q) (837)) (literal (valuationOf q) (845)) (countLit q [-80, -82, -84]) (countLit q [-86, -87, -90]) (count845 q) 1 (meaning837 q) (meaning845 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 845 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 842 = false ∨ valuationOf q 846 = true := by
  have hs : count845 q = (countLit q [-80, -82, -84]) + (countLit q [-86, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84]) (l₂ := [-86, -87, -90])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (842)) (literal (valuationOf q) (846)) (countLit q [-80, -82, -84]) (countLit q [-86, -87, -90]) (count845 q) 1 1 (meaning837 q) (meaning842 q) (meaning846 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 842 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 842 = false ∨ valuation q 846 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 843 = false ∨ valuationOf q 847 = true := by
  have hs : count845 q = (countLit q [-80, -82, -84]) + (countLit q [-86, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84]) (l₂ := [-86, -87, -90])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (843)) (literal (valuationOf q) (847)) (countLit q [-80, -82, -84]) (countLit q [-86, -87, -90]) (count845 q) 1 2 (meaning837 q) (meaning843 q) (meaning847 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 843 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 843 = false ∨ valuation q 847 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 846 = true := by
  have hs : count845 q = (countLit q [-80, -82, -84]) + (countLit q [-86, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84]) (l₂ := [-86, -87, -90])
  have hm := merge_left (literal (valuationOf q) (838)) (literal (valuationOf q) (846)) (countLit q [-80, -82, -84]) (countLit q [-86, -87, -90]) (count845 q) 2 (meaning838 q) (meaning846 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 846 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 842 = false ∨ valuationOf q 847 = true := by
  have hs : count845 q = (countLit q [-80, -82, -84]) + (countLit q [-86, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84]) (l₂ := [-86, -87, -90])
  have hm := merge_two (literal (valuationOf q) (838)) (literal (valuationOf q) (842)) (literal (valuationOf q) (847)) (countLit q [-80, -82, -84]) (countLit q [-86, -87, -90]) (count845 q) 2 1 (meaning838 q) (meaning842 q) (meaning847 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 842 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 842 = false ∨ valuation q 847 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 851 = true := by
  have hs : count851 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (851)) (countLit q [-95]) (countLit q [-97]) (count851 q) 1 (meaningNeg97 q) (meaning851 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 851 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 851 = true := by
  have hs : count851 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (851)) (countLit q [-95]) (countLit q [-97]) (count851 q) 1 (meaningNeg95 q) (meaning851 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 851 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 97 = true ∨ valuationOf q 852 = true := by
  have hs : count851 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (852)) (countLit q [-95]) (countLit q [-97]) (count851 q) 1 1 (meaningNeg95 q) (meaningNeg97 q) (meaning852 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 852 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 853 = true := by
  have hs : count853 q = (countLit q [-92]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuationOf q) (851)) (literal (valuationOf q) (853)) (countLit q [-92]) (countLit q [-95, -97]) (count853 q) 1 (meaning851 q) (meaning853 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 853 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 854 = true := by
  have hs : count853 q = (countLit q [-92]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuationOf q) (852)) (literal (valuationOf q) (854)) (countLit q [-92]) (countLit q [-95, -97]) (count853 q) 2 (meaning852 q) (meaning854 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 854 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 853 = true := by
  have hs : count853 q = (countLit q [-92]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-95, -97])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (853)) (countLit q [-92]) (countLit q [-95, -97]) (count853 q) 1 (meaningNeg92 q) (meaning853 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 853 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 851 = false ∨ valuationOf q 854 = true := by
  have hs : count853 q = (countLit q [-92]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (851)) (literal (valuationOf q) (854)) (countLit q [-92]) (countLit q [-95, -97]) (count853 q) 1 1 (meaningNeg92 q) (meaning851 q) (meaning854 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 851 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 851 = false ∨ valuation q 854 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 856 = true := by
  have hs : count856 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (856)) (countLit q [-98]) (countLit q [-99]) (count856 q) 1 (meaningNeg99 q) (meaning856 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 856 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 856 = true := by
  have hs : count856 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (856)) (countLit q [-98]) (countLit q [-99]) (count856 q) 1 (meaningNeg98 q) (meaning856 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 856 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 858 = true := by
  have hs : count858 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (858)) (countLit q [-104]) (countLit q [-105]) (count858 q) 1 (meaningNeg105 q) (meaning858 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 858 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 858 = true := by
  have hs : count858 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (858)) (countLit q [-104]) (countLit q [-105]) (count858 q) 1 (meaningNeg104 q) (meaning858 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 858 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 105 = true ∨ valuationOf q 859 = true := by
  have hs : count858 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (859)) (countLit q [-104]) (countLit q [-105]) (count858 q) 1 1 (meaningNeg104 q) (meaningNeg105 q) (meaning859 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 105 = true ∨ valuation q 859 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E075.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112075
