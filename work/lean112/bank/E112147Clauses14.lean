import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 802 = false ∨ valuationOf q 805 = true := by
  have hs : count803 q = (countLit q [-75]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (802)) (literal (valuationOf q) (805)) (countLit q [-75]) (countLit q [-77, -78]) (count803 q) 1 2 (meaningNeg75 q) (meaning802 q) (meaning805 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 802 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 802 = false ∨ valuation q 805 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 806 = true := by
  have hs : count806 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (806)) (countLit q [-83]) (countLit q [-85]) (count806 q) 1 (meaningNeg85 q) (meaning806 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 806 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 806 = true := by
  have hs : count806 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (806)) (countLit q [-83]) (countLit q [-85]) (count806 q) 1 (meaningNeg83 q) (meaning806 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 806 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 85 = true ∨ valuationOf q 807 = true := by
  have hs : count806 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (807)) (countLit q [-83]) (countLit q [-85]) (count806 q) 1 1 (meaningNeg83 q) (meaningNeg85 q) (meaning807 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 85 = true ∨ valuation q 807 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 806 = false ∨ valuationOf q 808 = true := by
  have hs : count808 q = (countLit q [-79]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-83, -85])
  have hm := merge_right (literal (valuationOf q) (806)) (literal (valuationOf q) (808)) (countLit q [-79]) (countLit q [-83, -85]) (count808 q) 1 (meaning806 q) (meaning808 q) hs
  change valuationOf q 806 = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 806 = false ∨ valuation q 808 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 807 = false ∨ valuationOf q 809 = true := by
  have hs : count808 q = (countLit q [-79]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-83, -85])
  have hm := merge_right (literal (valuationOf q) (807)) (literal (valuationOf q) (809)) (countLit q [-79]) (countLit q [-83, -85]) (count808 q) 2 (meaning807 q) (meaning809 q) hs
  change valuationOf q 807 = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 807 = false ∨ valuation q 809 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 808 = true := by
  have hs : count808 q = (countLit q [-79]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-83, -85])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (808)) (countLit q [-79]) (countLit q [-83, -85]) (count808 q) 1 (meaningNeg79 q) (meaning808 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 808 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 806 = false ∨ valuationOf q 809 = true := by
  have hs : count808 q = (countLit q [-79]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-83, -85])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (806)) (literal (valuationOf q) (809)) (countLit q [-79]) (countLit q [-83, -85]) (count808 q) 1 1 (meaningNeg79 q) (meaning806 q) (meaning809 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 806 = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 806 = false ∨ valuation q 809 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 808 = false ∨ valuationOf q 811 = true := by
  have hs : count811 q = (countLit q [-75, -77, -78]) + (countLit q [-79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78]) (l₂ := [-79, -83, -85])
  have hm := merge_right (literal (valuationOf q) (808)) (literal (valuationOf q) (811)) (countLit q [-75, -77, -78]) (countLit q [-79, -83, -85]) (count811 q) 1 (meaning808 q) (meaning811 q) hs
  change valuationOf q 808 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 808 = false ∨ valuation q 811 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 812 = true := by
  have hs : count811 q = (countLit q [-75, -77, -78]) + (countLit q [-79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78]) (l₂ := [-79, -83, -85])
  have hm := merge_right (literal (valuationOf q) (809)) (literal (valuationOf q) (812)) (countLit q [-75, -77, -78]) (countLit q [-79, -83, -85]) (count811 q) 2 (meaning809 q) (meaning812 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 812 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 811 = true := by
  have hs : count811 q = (countLit q [-75, -77, -78]) + (countLit q [-79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78]) (l₂ := [-79, -83, -85])
  have hm := merge_left (literal (valuationOf q) (803)) (literal (valuationOf q) (811)) (countLit q [-75, -77, -78]) (countLit q [-79, -83, -85]) (count811 q) 1 (meaning803 q) (meaning811 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 811 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 808 = false ∨ valuationOf q 812 = true := by
  have hs : count811 q = (countLit q [-75, -77, -78]) + (countLit q [-79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78]) (l₂ := [-79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (808)) (literal (valuationOf q) (812)) (countLit q [-75, -77, -78]) (countLit q [-79, -83, -85]) (count811 q) 1 1 (meaning803 q) (meaning808 q) (meaning812 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 808 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 808 = false ∨ valuation q 812 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 809 = false ∨ valuationOf q 813 = true := by
  have hs : count811 q = (countLit q [-75, -77, -78]) + (countLit q [-79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78]) (l₂ := [-79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (809)) (literal (valuationOf q) (813)) (countLit q [-75, -77, -78]) (countLit q [-79, -83, -85]) (count811 q) 1 2 (meaning803 q) (meaning809 q) (meaning813 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 809 = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 809 = false ∨ valuation q 813 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 812 = true := by
  have hs : count811 q = (countLit q [-75, -77, -78]) + (countLit q [-79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78]) (l₂ := [-79, -83, -85])
  have hm := merge_left (literal (valuationOf q) (804)) (literal (valuationOf q) (812)) (countLit q [-75, -77, -78]) (countLit q [-79, -83, -85]) (count811 q) 2 (meaning804 q) (meaning812 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 812 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 808 = false ∨ valuationOf q 813 = true := by
  have hs : count811 q = (countLit q [-75, -77, -78]) + (countLit q [-79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78]) (l₂ := [-79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (808)) (literal (valuationOf q) (813)) (countLit q [-75, -77, -78]) (countLit q [-79, -83, -85]) (count811 q) 2 1 (meaning804 q) (meaning808 q) (meaning813 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 808 = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 808 = false ∨ valuation q 813 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 813 = true := by
  have hs : count811 q = (countLit q [-75, -77, -78]) + (countLit q [-79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78]) (l₂ := [-79, -83, -85])
  have hm := merge_left (literal (valuationOf q) (805)) (literal (valuationOf q) (813)) (countLit q [-75, -77, -78]) (countLit q [-79, -83, -85]) (count811 q) 3 (meaning805 q) (meaning813 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 813 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 817 = true := by
  have hs : count817 q = (countLit q [-89]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (817)) (countLit q [-89]) (countLit q [-90]) (count817 q) 1 (meaningNeg90 q) (meaning817 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 817 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 819 = true := by
  have hs : count819 q = (countLit q [-87]) + (countLit q [-89, -90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89, -90])
  have hm := merge_right (literal (valuationOf q) (817)) (literal (valuationOf q) (819)) (countLit q [-87]) (countLit q [-89, -90]) (count819 q) 1 (meaning817 q) (meaning819 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 819 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 819 = true := by
  have hs : count819 q = (countLit q [-87]) + (countLit q [-89, -90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89, -90])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (819)) (countLit q [-87]) (countLit q [-89, -90]) (count819 q) 1 (meaningNeg87 q) (meaning819 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 819 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 817 = false ∨ valuationOf q 820 = true := by
  have hs : count819 q = (countLit q [-87]) + (countLit q [-89, -90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89, -90])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (817)) (literal (valuationOf q) (820)) (countLit q [-87]) (countLit q [-89, -90]) (count819 q) 1 1 (meaningNeg87 q) (meaning817 q) (meaning820 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 817 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 817 = false ∨ valuation q 820 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 822 = true := by
  have hs : count822 q = (countLit q [-92]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (822)) (countLit q [-92]) (countLit q [-94]) (count822 q) 1 (meaningNeg94 q) (meaning822 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 822 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 824 = true := by
  have hs : count824 q = (countLit q [-96]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (824)) (countLit q [-96]) (countLit q [-99]) (count824 q) 1 (meaningNeg99 q) (meaning824 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 824 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 824 = true := by
  have hs : count824 q = (countLit q [-96]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (824)) (countLit q [-96]) (countLit q [-99]) (count824 q) 1 (meaningNeg96 q) (meaning824 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 824 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 826 = true := by
  have hs : count826 q = (countLit q [-92, -94]) + (countLit q [-96, -99]) := List.countP_append (p := literal q) (l₁ := [-92, -94]) (l₂ := [-96, -99])
  have hm := merge_right (literal (valuationOf q) (824)) (literal (valuationOf q) (826)) (countLit q [-92, -94]) (countLit q [-96, -99]) (count826 q) 1 (meaning824 q) (meaning826 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 826 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 826 = true := by
  have hs : count826 q = (countLit q [-92, -94]) + (countLit q [-96, -99]) := List.countP_append (p := literal q) (l₁ := [-92, -94]) (l₂ := [-96, -99])
  have hm := merge_left (literal (valuationOf q) (822)) (literal (valuationOf q) (826)) (countLit q [-92, -94]) (countLit q [-96, -99]) (count826 q) 1 (meaning822 q) (meaning826 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 826 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 824 = false ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-92, -94]) + (countLit q [-96, -99]) := List.countP_append (p := literal q) (l₁ := [-92, -94]) (l₂ := [-96, -99])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (824)) (literal (valuationOf q) (827)) (countLit q [-92, -94]) (countLit q [-96, -99]) (count826 q) 1 1 (meaning822 q) (meaning824 q) (meaning827 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 824 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 824 = false ∨ valuation q 827 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 830 = true := by
  have hs : count830 q = (countLit q [-87, -89, -90]) + (countLit q [-92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -90]) (l₂ := [-92, -94, -96, -99])
  have hm := merge_right (literal (valuationOf q) (826)) (literal (valuationOf q) (830)) (countLit q [-87, -89, -90]) (countLit q [-92, -94, -96, -99]) (count830 q) 1 (meaning826 q) (meaning830 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 830 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-87, -89, -90]) + (countLit q [-92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -90]) (l₂ := [-92, -94, -96, -99])
  have hm := merge_right (literal (valuationOf q) (827)) (literal (valuationOf q) (831)) (countLit q [-87, -89, -90]) (countLit q [-92, -94, -96, -99]) (count830 q) 2 (meaning827 q) (meaning831 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 831 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 830 = true := by
  have hs : count830 q = (countLit q [-87, -89, -90]) + (countLit q [-92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -90]) (l₂ := [-92, -94, -96, -99])
  have hm := merge_left (literal (valuationOf q) (819)) (literal (valuationOf q) (830)) (countLit q [-87, -89, -90]) (countLit q [-92, -94, -96, -99]) (count830 q) 1 (meaning819 q) (meaning830 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 830 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 826 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-87, -89, -90]) + (countLit q [-92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -90]) (l₂ := [-92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (819)) (literal (valuationOf q) (826)) (literal (valuationOf q) (831)) (countLit q [-87, -89, -90]) (countLit q [-92, -94, -96, -99]) (count830 q) 1 1 (meaning819 q) (meaning826 q) (meaning831 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 826 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 826 = false ∨ valuation q 831 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-87, -89, -90]) + (countLit q [-92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-87, -89, -90]) (l₂ := [-92, -94, -96, -99])
  have hm := merge_left (literal (valuationOf q) (820)) (literal (valuationOf q) (831)) (countLit q [-87, -89, -90]) (countLit q [-92, -94, -96, -99]) (count830 q) 2 (meaning820 q) (meaning831 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 831 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 830 = false ∨ valuationOf q 837 = true := by
  have hs : count837 q = (countLit q [-75, -77, -78, -79, -83, -85]) + (countLit q [-87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78, -79, -83, -85]) (l₂ := [-87, -89, -90, -92, -94, -96, -99])
  have hm := merge_right (literal (valuationOf q) (830)) (literal (valuationOf q) (837)) (countLit q [-75, -77, -78, -79, -83, -85]) (countLit q [-87, -89, -90, -92, -94, -96, -99]) (count837 q) 1 (meaning830 q) (meaning837 q) hs
  change valuationOf q 830 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 830 = false ∨ valuation q 837 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E147.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112147
