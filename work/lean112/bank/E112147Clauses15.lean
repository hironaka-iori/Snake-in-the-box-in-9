import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 837 = true := by
  have hs : count837 q = (countLit q [-75, -77, -78, -79, -83, -85]) + (countLit q [-87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78, -79, -83, -85]) (l₂ := [-87, -89, -90, -92, -94, -96, -99])
  have hm := merge_left (literal (valuationOf q) (811)) (literal (valuationOf q) (837)) (countLit q [-75, -77, -78, -79, -83, -85]) (countLit q [-87, -89, -90, -92, -94, -96, -99]) (count837 q) 1 (meaning811 q) (meaning837 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 837 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 830 = false ∨ valuationOf q 838 = true := by
  have hs : count837 q = (countLit q [-75, -77, -78, -79, -83, -85]) + (countLit q [-87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78, -79, -83, -85]) (l₂ := [-87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (830)) (literal (valuationOf q) (838)) (countLit q [-75, -77, -78, -79, -83, -85]) (countLit q [-87, -89, -90, -92, -94, -96, -99]) (count837 q) 1 1 (meaning811 q) (meaning830 q) (meaning838 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 830 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 830 = false ∨ valuation q 838 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 831 = false ∨ valuationOf q 839 = true := by
  have hs : count837 q = (countLit q [-75, -77, -78, -79, -83, -85]) + (countLit q [-87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78, -79, -83, -85]) (l₂ := [-87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (831)) (literal (valuationOf q) (839)) (countLit q [-75, -77, -78, -79, -83, -85]) (countLit q [-87, -89, -90, -92, -94, -96, -99]) (count837 q) 1 2 (meaning811 q) (meaning831 q) (meaning839 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 831 = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 831 = false ∨ valuation q 839 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 838 = true := by
  have hs : count837 q = (countLit q [-75, -77, -78, -79, -83, -85]) + (countLit q [-87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78, -79, -83, -85]) (l₂ := [-87, -89, -90, -92, -94, -96, -99])
  have hm := merge_left (literal (valuationOf q) (812)) (literal (valuationOf q) (838)) (countLit q [-75, -77, -78, -79, -83, -85]) (countLit q [-87, -89, -90, -92, -94, -96, -99]) (count837 q) 2 (meaning812 q) (meaning838 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 838 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 830 = false ∨ valuationOf q 839 = true := by
  have hs : count837 q = (countLit q [-75, -77, -78, -79, -83, -85]) + (countLit q [-87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78, -79, -83, -85]) (l₂ := [-87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (830)) (literal (valuationOf q) (839)) (countLit q [-75, -77, -78, -79, -83, -85]) (countLit q [-87, -89, -90, -92, -94, -96, -99]) (count837 q) 2 1 (meaning812 q) (meaning830 q) (meaning839 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 830 = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 830 = false ∨ valuation q 839 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 831 = false ∨ valuationOf q 840 = true := by
  have hs : count837 q = (countLit q [-75, -77, -78, -79, -83, -85]) + (countLit q [-87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78, -79, -83, -85]) (l₂ := [-87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (831)) (literal (valuationOf q) (840)) (countLit q [-75, -77, -78, -79, -83, -85]) (countLit q [-87, -89, -90, -92, -94, -96, -99]) (count837 q) 2 2 (meaning812 q) (meaning831 q) (meaning840 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 831 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 831 = false ∨ valuation q 840 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 839 = true := by
  have hs : count837 q = (countLit q [-75, -77, -78, -79, -83, -85]) + (countLit q [-87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78, -79, -83, -85]) (l₂ := [-87, -89, -90, -92, -94, -96, -99])
  have hm := merge_left (literal (valuationOf q) (813)) (literal (valuationOf q) (839)) (countLit q [-75, -77, -78, -79, -83, -85]) (countLit q [-87, -89, -90, -92, -94, -96, -99]) (count837 q) 3 (meaning813 q) (meaning839 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 839 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 830 = false ∨ valuationOf q 840 = true := by
  have hs : count837 q = (countLit q [-75, -77, -78, -79, -83, -85]) + (countLit q [-87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-75, -77, -78, -79, -83, -85]) (l₂ := [-87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (830)) (literal (valuationOf q) (840)) (countLit q [-75, -77, -78, -79, -83, -85]) (countLit q [-87, -89, -90, -92, -94, -96, -99]) (count837 q) 3 1 (meaning813 q) (meaning830 q) (meaning840 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 830 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 830 = false ∨ valuation q 840 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 846 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_right (literal (valuationOf q) (837)) (literal (valuationOf q) (846)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 1 (meaning837 q) (meaning846 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 846 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 847 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_right (literal (valuationOf q) (838)) (literal (valuationOf q) (847)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 2 (meaning838 q) (meaning847 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 847 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 848 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_right (literal (valuationOf q) (839)) (literal (valuationOf q) (848)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 3 (meaning839 q) (meaning848 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 848 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 849 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_right (literal (valuationOf q) (840)) (literal (valuationOf q) (849)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 4 (meaning840 q) (meaning849 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 849 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 837 = false ∨ valuationOf q 847 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (792)) (literal (valuationOf q) (837)) (literal (valuationOf q) (847)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 1 1 (meaning792 q) (meaning837 q) (meaning847 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 837 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 837 = false ∨ valuation q 847 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 838 = false ∨ valuationOf q 848 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (792)) (literal (valuationOf q) (838)) (literal (valuationOf q) (848)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 1 2 (meaning792 q) (meaning838 q) (meaning848 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 838 = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 838 = false ∨ valuation q 848 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 839 = false ∨ valuationOf q 849 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (792)) (literal (valuationOf q) (839)) (literal (valuationOf q) (849)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 1 3 (meaning792 q) (meaning839 q) (meaning849 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 839 = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 839 = false ∨ valuation q 849 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 840 = false ∨ valuationOf q 850 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (792)) (literal (valuationOf q) (840)) (literal (valuationOf q) (850)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 1 4 (meaning792 q) (meaning840 q) (meaning850 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 840 = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 840 = false ∨ valuation q 850 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 793 = false ∨ valuationOf q 847 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_left (literal (valuationOf q) (793)) (literal (valuationOf q) (847)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 2 (meaning793 q) (meaning847 q) hs
  change valuationOf q 793 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 793 = false ∨ valuation q 847 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 793 = false ∨ valuationOf q 837 = false ∨ valuationOf q 848 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (793)) (literal (valuationOf q) (837)) (literal (valuationOf q) (848)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 2 1 (meaning793 q) (meaning837 q) (meaning848 q) hs
  change valuationOf q 793 = false ∨ valuationOf q 837 = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 793 = false ∨ valuation q 837 = false ∨ valuation q 848 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 793 = false ∨ valuationOf q 838 = false ∨ valuationOf q 849 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (793)) (literal (valuationOf q) (838)) (literal (valuationOf q) (849)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 2 2 (meaning793 q) (meaning838 q) (meaning849 q) hs
  change valuationOf q 793 = false ∨ valuationOf q 838 = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 793 = false ∨ valuation q 838 = false ∨ valuation q 849 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 793 = false ∨ valuationOf q 839 = false ∨ valuationOf q 850 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (793)) (literal (valuationOf q) (839)) (literal (valuationOf q) (850)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 2 3 (meaning793 q) (meaning839 q) (meaning850 q) hs
  change valuationOf q 793 = false ∨ valuationOf q 839 = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 793 = false ∨ valuation q 839 = false ∨ valuation q 850 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 794 = false ∨ valuationOf q 848 = true := by
  have hs : count846 q = (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) + (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (l₂ := [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_left (literal (valuationOf q) (794)) (literal (valuationOf q) (848)) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]) (countLit q [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count846 q) 3 (meaning794 q) (meaning848 q) hs
  change valuationOf q 794 = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 794 = false ∨ valuation q 848 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 754 = false ∨ valuationOf q 850 = false ∨ valuationOf q 863 = true := by
  have hs : count855 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) + (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (l₂ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (754)) (literal (valuationOf q) (850)) (literal (valuationOf q) (863)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count855 q) 4 5 (meaning754 q) (meaning850 q) (meaning863 q) hs
  change valuationOf q 754 = false ∨ valuationOf q 850 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 754 = false ∨ valuation q 850 = false ∨ valuation q 863 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 755 = false ∨ valuationOf q 849 = false ∨ valuationOf q 863 = true := by
  have hs : count855 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) + (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (l₂ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (755)) (literal (valuationOf q) (849)) (literal (valuationOf q) (863)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count855 q) 5 4 (meaning755 q) (meaning849 q) (meaning863 q) hs
  change valuationOf q 755 = false ∨ valuationOf q 849 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 755 = false ∨ valuation q 849 = false ∨ valuation q 863 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 756 = false ∨ valuationOf q 848 = false ∨ valuationOf q 863 = true := by
  have hs : count855 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) + (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (l₂ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (756)) (literal (valuationOf q) (848)) (literal (valuationOf q) (863)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count855 q) 6 3 (meaning756 q) (meaning848 q) (meaning863 q) hs
  change valuationOf q 756 = false ∨ valuationOf q 848 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 756 = false ∨ valuation q 848 = false ∨ valuation q 863 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 757 = false ∨ valuationOf q 847 = false ∨ valuationOf q 863 = true := by
  have hs : count855 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) + (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (l₂ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (757)) (literal (valuationOf q) (847)) (literal (valuationOf q) (863)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count855 q) 7 2 (meaning757 q) (meaning847 q) (meaning863 q) hs
  change valuationOf q 757 = false ∨ valuationOf q 847 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 757 = false ∨ valuation q 847 = false ∨ valuation q 863 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 846 = false ∨ valuationOf q 863 = true := by
  have hs : count855 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) + (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (l₂ := [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99])
  have hm := merge_two (literal (valuationOf q) (758)) (literal (valuationOf q) (846)) (literal (valuationOf q) (863)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (countLit q [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]) (count855 q) 8 1 (meaning758 q) (meaning846 q) (meaning863 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 846 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 846 = false ∨ valuation q 863 = true := counterClause506 (baseVal q)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 863 = false := by
  rw [value863]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count855 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value10, value11, value18, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (164 : Vertex) (166 : Vertex) (180 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value14, value15, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (170 : Vertex) (171 : Vertex) (186 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value33, value34, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (238 : Vertex) (239 : Vertex) (254 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value42, value43, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (257 : Vertex) (264 : Vertex) (265 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E147.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h⟩

end
end Snake9.Regrowth.E112147
