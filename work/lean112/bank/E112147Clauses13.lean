import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 760 = true := by
  have hs : count760 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (760)) (countLit q [-50]) (countLit q [-52]) (count760 q) 1 (meaningNeg52 q) (meaning760 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 760 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 760 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 760 = true := by
  have hs : count760 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (760)) (countLit q [-50]) (countLit q [-52]) (count760 q) 1 (meaningNeg50 q) (meaning760 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 760 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 760 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 52 = true ∨ valuationOf q 761 = true := by
  have hs : count760 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (761)) (countLit q [-50]) (countLit q [-52]) (count760 q) 1 1 (meaningNeg50 q) (meaningNeg52 q) (meaning761 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 761 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 52 = true ∨ valuation q 761 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 760 = false ∨ valuationOf q 762 = true := by
  have hs : count762 q = (countLit q [-48]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50, -52])
  have hm := merge_right (literal (valuationOf q) (760)) (literal (valuationOf q) (762)) (countLit q [-48]) (countLit q [-50, -52]) (count762 q) 1 (meaning760 q) (meaning762 q) hs
  change valuationOf q 760 = false ∨ valuationOf q 762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 760 = false ∨ valuation q 762 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 761 = false ∨ valuationOf q 763 = true := by
  have hs : count762 q = (countLit q [-48]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50, -52])
  have hm := merge_right (literal (valuationOf q) (761)) (literal (valuationOf q) (763)) (countLit q [-48]) (countLit q [-50, -52]) (count762 q) 2 (meaning761 q) (meaning763 q) hs
  change valuationOf q 761 = false ∨ valuationOf q 763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 761 = false ∨ valuation q 763 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 762 = true := by
  have hs : count762 q = (countLit q [-48]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50, -52])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (762)) (countLit q [-48]) (countLit q [-50, -52]) (count762 q) 1 (meaningNeg48 q) (meaning762 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 762 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 762 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 765 = true := by
  have hs : count765 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (765)) (countLit q [-58]) (countLit q [-60]) (count765 q) 1 (meaningNeg60 q) (meaning765 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 765 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 765 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 765 = true := by
  have hs : count765 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (765)) (countLit q [-58]) (countLit q [-60]) (count765 q) 1 (meaningNeg58 q) (meaning765 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 765 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 765 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 765 = false ∨ valuationOf q 767 = true := by
  have hs : count767 q = (countLit q [-55]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58, -60])
  have hm := merge_right (literal (valuationOf q) (765)) (literal (valuationOf q) (767)) (countLit q [-55]) (countLit q [-58, -60]) (count767 q) 1 (meaning765 q) (meaning767 q) hs
  change valuationOf q 765 = false ∨ valuationOf q 767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 765 = false ∨ valuation q 767 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 767 = true := by
  have hs : count767 q = (countLit q [-55]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58, -60])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (767)) (countLit q [-55]) (countLit q [-58, -60]) (count767 q) 1 (meaningNeg55 q) (meaning767 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 767 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 767 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 767 = false ∨ valuationOf q 770 = true := by
  have hs : count770 q = (countLit q [-48, -50, -52]) + (countLit q [-55, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52]) (l₂ := [-55, -58, -60])
  have hm := merge_right (literal (valuationOf q) (767)) (literal (valuationOf q) (770)) (countLit q [-48, -50, -52]) (countLit q [-55, -58, -60]) (count770 q) 1 (meaning767 q) (meaning770 q) hs
  change valuationOf q 767 = false ∨ valuationOf q 770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 767 = false ∨ valuation q 770 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 762 = false ∨ valuationOf q 770 = true := by
  have hs : count770 q = (countLit q [-48, -50, -52]) + (countLit q [-55, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52]) (l₂ := [-55, -58, -60])
  have hm := merge_left (literal (valuationOf q) (762)) (literal (valuationOf q) (770)) (countLit q [-48, -50, -52]) (countLit q [-55, -58, -60]) (count770 q) 1 (meaning762 q) (meaning770 q) hs
  change valuationOf q 762 = false ∨ valuationOf q 770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 762 = false ∨ valuation q 770 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 762 = false ∨ valuationOf q 767 = false ∨ valuationOf q 771 = true := by
  have hs : count770 q = (countLit q [-48, -50, -52]) + (countLit q [-55, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52]) (l₂ := [-55, -58, -60])
  have hm := merge_two (literal (valuationOf q) (762)) (literal (valuationOf q) (767)) (literal (valuationOf q) (771)) (countLit q [-48, -50, -52]) (countLit q [-55, -58, -60]) (count770 q) 1 1 (meaning762 q) (meaning767 q) (meaning771 q) hs
  change valuationOf q 762 = false ∨ valuationOf q 767 = false ∨ valuationOf q 771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 762 = false ∨ valuation q 767 = false ∨ valuation q 771 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 763 = false ∨ valuationOf q 771 = true := by
  have hs : count770 q = (countLit q [-48, -50, -52]) + (countLit q [-55, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52]) (l₂ := [-55, -58, -60])
  have hm := merge_left (literal (valuationOf q) (763)) (literal (valuationOf q) (771)) (countLit q [-48, -50, -52]) (countLit q [-55, -58, -60]) (count770 q) 2 (meaning763 q) (meaning771 q) hs
  change valuationOf q 763 = false ∨ valuationOf q 771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 763 = false ∨ valuation q 771 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 778 = true := by
  have hs : count778 q = (countLit q [-61]) + (countLit q [-63, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63, -65])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (778)) (countLit q [-61]) (countLit q [-63, -65]) (count778 q) 1 (meaningNeg61 q) (meaning778 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 778 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 781 = true := by
  have hs : count781 q = (countLit q [-69]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (781)) (countLit q [-69]) (countLit q [-73]) (count781 q) 1 (meaningNeg73 q) (meaning781 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 781 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 781 = false ∨ valuationOf q 783 = true := by
  have hs : count783 q = (countLit q [-67]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69, -73])
  have hm := merge_right (literal (valuationOf q) (781)) (literal (valuationOf q) (783)) (countLit q [-67]) (countLit q [-69, -73]) (count783 q) 1 (meaning781 q) (meaning783 q) hs
  change valuationOf q 781 = false ∨ valuationOf q 783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 781 = false ∨ valuation q 783 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 783 = false ∨ valuationOf q 786 = true := by
  have hs : count786 q = (countLit q [-61, -63, -65]) + (countLit q [-67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -65]) (l₂ := [-67, -69, -73])
  have hm := merge_right (literal (valuationOf q) (783)) (literal (valuationOf q) (786)) (countLit q [-61, -63, -65]) (countLit q [-67, -69, -73]) (count786 q) 1 (meaning783 q) (meaning786 q) hs
  change valuationOf q 783 = false ∨ valuationOf q 786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 783 = false ∨ valuation q 786 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 778 = false ∨ valuationOf q 783 = false ∨ valuationOf q 787 = true := by
  have hs : count786 q = (countLit q [-61, -63, -65]) + (countLit q [-67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -65]) (l₂ := [-67, -69, -73])
  have hm := merge_two (literal (valuationOf q) (778)) (literal (valuationOf q) (783)) (literal (valuationOf q) (787)) (countLit q [-61, -63, -65]) (countLit q [-67, -69, -73]) (count786 q) 1 1 (meaning778 q) (meaning783 q) (meaning787 q) hs
  change valuationOf q 778 = false ∨ valuationOf q 783 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 778 = false ∨ valuation q 783 = false ∨ valuation q 787 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 786 = false ∨ valuationOf q 792 = true := by
  have hs : count792 q = (countLit q [-48, -50, -52, -55, -58, -60]) + (countLit q [-61, -63, -65, -67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60]) (l₂ := [-61, -63, -65, -67, -69, -73])
  have hm := merge_right (literal (valuationOf q) (786)) (literal (valuationOf q) (792)) (countLit q [-48, -50, -52, -55, -58, -60]) (countLit q [-61, -63, -65, -67, -69, -73]) (count792 q) 1 (meaning786 q) (meaning792 q) hs
  change valuationOf q 786 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 786 = false ∨ valuation q 792 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 787 = false ∨ valuationOf q 793 = true := by
  have hs : count792 q = (countLit q [-48, -50, -52, -55, -58, -60]) + (countLit q [-61, -63, -65, -67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60]) (l₂ := [-61, -63, -65, -67, -69, -73])
  have hm := merge_right (literal (valuationOf q) (787)) (literal (valuationOf q) (793)) (countLit q [-48, -50, -52, -55, -58, -60]) (countLit q [-61, -63, -65, -67, -69, -73]) (count792 q) 2 (meaning787 q) (meaning793 q) hs
  change valuationOf q 787 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 787 = false ∨ valuation q 793 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 770 = false ∨ valuationOf q 792 = true := by
  have hs : count792 q = (countLit q [-48, -50, -52, -55, -58, -60]) + (countLit q [-61, -63, -65, -67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60]) (l₂ := [-61, -63, -65, -67, -69, -73])
  have hm := merge_left (literal (valuationOf q) (770)) (literal (valuationOf q) (792)) (countLit q [-48, -50, -52, -55, -58, -60]) (countLit q [-61, -63, -65, -67, -69, -73]) (count792 q) 1 (meaning770 q) (meaning792 q) hs
  change valuationOf q 770 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 770 = false ∨ valuation q 792 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 770 = false ∨ valuationOf q 786 = false ∨ valuationOf q 793 = true := by
  have hs : count792 q = (countLit q [-48, -50, -52, -55, -58, -60]) + (countLit q [-61, -63, -65, -67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60]) (l₂ := [-61, -63, -65, -67, -69, -73])
  have hm := merge_two (literal (valuationOf q) (770)) (literal (valuationOf q) (786)) (literal (valuationOf q) (793)) (countLit q [-48, -50, -52, -55, -58, -60]) (countLit q [-61, -63, -65, -67, -69, -73]) (count792 q) 1 1 (meaning770 q) (meaning786 q) (meaning793 q) hs
  change valuationOf q 770 = false ∨ valuationOf q 786 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 770 = false ∨ valuation q 786 = false ∨ valuation q 793 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 771 = false ∨ valuationOf q 793 = true := by
  have hs : count792 q = (countLit q [-48, -50, -52, -55, -58, -60]) + (countLit q [-61, -63, -65, -67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60]) (l₂ := [-61, -63, -65, -67, -69, -73])
  have hm := merge_left (literal (valuationOf q) (771)) (literal (valuationOf q) (793)) (countLit q [-48, -50, -52, -55, -58, -60]) (countLit q [-61, -63, -65, -67, -69, -73]) (count792 q) 2 (meaning771 q) (meaning793 q) hs
  change valuationOf q 771 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 771 = false ∨ valuation q 793 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 771 = false ∨ valuationOf q 786 = false ∨ valuationOf q 794 = true := by
  have hs : count792 q = (countLit q [-48, -50, -52, -55, -58, -60]) + (countLit q [-61, -63, -65, -67, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-48, -50, -52, -55, -58, -60]) (l₂ := [-61, -63, -65, -67, -69, -73])
  have hm := merge_two (literal (valuationOf q) (771)) (literal (valuationOf q) (786)) (literal (valuationOf q) (794)) (countLit q [-48, -50, -52, -55, -58, -60]) (countLit q [-61, -63, -65, -67, -69, -73]) (count792 q) 2 1 (meaning771 q) (meaning786 q) (meaning794 q) hs
  change valuationOf q 771 = false ∨ valuationOf q 786 = false ∨ valuationOf q 794 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 771 = false ∨ valuation q 786 = false ∨ valuation q 794 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 801 = true := by
  have hs : count801 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (801)) (countLit q [-77]) (countLit q [-78]) (count801 q) 1 (meaningNeg78 q) (meaning801 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 801 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 801 = true := by
  have hs : count801 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (801)) (countLit q [-77]) (countLit q [-78]) (count801 q) 1 (meaningNeg77 q) (meaning801 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 801 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 78 = true ∨ valuationOf q 802 = true := by
  have hs : count801 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (802)) (countLit q [-77]) (countLit q [-78]) (count801 q) 1 1 (meaningNeg77 q) (meaningNeg78 q) (meaning802 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 78 = true ∨ valuation q 802 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 803 = true := by
  have hs : count803 q = (countLit q [-75]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (801)) (literal (valuationOf q) (803)) (countLit q [-75]) (countLit q [-77, -78]) (count803 q) 1 (meaning801 q) (meaning803 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 803 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 804 = true := by
  have hs : count803 q = (countLit q [-75]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (802)) (literal (valuationOf q) (804)) (countLit q [-75]) (countLit q [-77, -78]) (count803 q) 2 (meaning802 q) (meaning804 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 804 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 803 = true := by
  have hs : count803 q = (countLit q [-75]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (803)) (countLit q [-75]) (countLit q [-77, -78]) (count803 q) 1 (meaningNeg75 q) (meaning803 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 803 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 801 = false ∨ valuationOf q 804 = true := by
  have hs : count803 q = (countLit q [-75]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (801)) (literal (valuationOf q) (804)) (countLit q [-75]) (countLit q [-77, -78]) (count803 q) 1 1 (meaningNeg75 q) (meaning801 q) (meaning804 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 801 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 801 = false ∨ valuation q 804 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E147.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112147
