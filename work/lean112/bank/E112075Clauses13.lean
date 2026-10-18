import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 811 = true := by
  have hs : count811 q = (countLit q [-69]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (809)) (literal (valuationOf q) (811)) (countLit q [-69]) (countLit q [-71, -73]) (count811 q) 1 (meaning809 q) (meaning811 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 811 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 812 = true := by
  have hs : count811 q = (countLit q [-69]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (810)) (literal (valuationOf q) (812)) (countLit q [-69]) (countLit q [-71, -73]) (count811 q) 2 (meaning810 q) (meaning812 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 812 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 814 = true := by
  have hs : count814 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (814)) (countLit q [-78]) (countLit q [-79]) (count814 q) 1 (meaningNeg79 q) (meaning814 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 814 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 814 = true := by
  have hs : count814 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (814)) (countLit q [-78]) (countLit q [-79]) (count814 q) 1 (meaningNeg78 q) (meaning814 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 814 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 79 = true ∨ valuationOf q 815 = true := by
  have hs : count814 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (815)) (countLit q [-78]) (countLit q [-79]) (count814 q) 1 1 (meaningNeg78 q) (meaningNeg79 q) (meaning815 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 815 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 79 = true ∨ valuation q 815 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 816 = true := by
  have hs : count816 q = (countLit q [-76]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (814)) (literal (valuationOf q) (816)) (countLit q [-76]) (countLit q [-78, -79]) (count816 q) 1 (meaning814 q) (meaning816 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 816 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 817 = true := by
  have hs : count816 q = (countLit q [-76]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (815)) (literal (valuationOf q) (817)) (countLit q [-76]) (countLit q [-78, -79]) (count816 q) 2 (meaning815 q) (meaning817 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 817 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 816 = true := by
  have hs : count816 q = (countLit q [-76]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78, -79])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (816)) (countLit q [-76]) (countLit q [-78, -79]) (count816 q) 1 (meaningNeg76 q) (meaning816 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 816 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 814 = false ∨ valuationOf q 817 = true := by
  have hs : count816 q = (countLit q [-76]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (814)) (literal (valuationOf q) (817)) (countLit q [-76]) (countLit q [-78, -79]) (count816 q) 1 1 (meaningNeg76 q) (meaning814 q) (meaning817 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 814 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 814 = false ∨ valuation q 817 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 815 = false ∨ valuationOf q 818 = true := by
  have hs : count816 q = (countLit q [-76]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (815)) (literal (valuationOf q) (818)) (countLit q [-76]) (countLit q [-78, -79]) (count816 q) 1 2 (meaningNeg76 q) (meaning815 q) (meaning818 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 815 = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 815 = false ∨ valuation q 818 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 819 = true := by
  have hs : count819 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -78, -79])
  have hm := merge_right (literal (valuationOf q) (816)) (literal (valuationOf q) (819)) (countLit q [-69, -71, -73]) (countLit q [-76, -78, -79]) (count819 q) 1 (meaning816 q) (meaning819 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 819 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 820 = true := by
  have hs : count819 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -78, -79])
  have hm := merge_right (literal (valuationOf q) (817)) (literal (valuationOf q) (820)) (countLit q [-69, -71, -73]) (countLit q [-76, -78, -79]) (count819 q) 2 (meaning817 q) (meaning820 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 820 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 818 = false ∨ valuationOf q 821 = true := by
  have hs : count819 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -78, -79])
  have hm := merge_right (literal (valuationOf q) (818)) (literal (valuationOf q) (821)) (countLit q [-69, -71, -73]) (countLit q [-76, -78, -79]) (count819 q) 3 (meaning818 q) (meaning821 q) hs
  change valuationOf q 818 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 818 = false ∨ valuation q 821 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 819 = true := by
  have hs : count819 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -78, -79])
  have hm := merge_left (literal (valuationOf q) (811)) (literal (valuationOf q) (819)) (countLit q [-69, -71, -73]) (countLit q [-76, -78, -79]) (count819 q) 1 (meaning811 q) (meaning819 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 819 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 816 = false ∨ valuationOf q 820 = true := by
  have hs : count819 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (816)) (literal (valuationOf q) (820)) (countLit q [-69, -71, -73]) (countLit q [-76, -78, -79]) (count819 q) 1 1 (meaning811 q) (meaning816 q) (meaning820 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 816 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 816 = false ∨ valuation q 820 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 817 = false ∨ valuationOf q 821 = true := by
  have hs : count819 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (817)) (literal (valuationOf q) (821)) (countLit q [-69, -71, -73]) (countLit q [-76, -78, -79]) (count819 q) 1 2 (meaning811 q) (meaning817 q) (meaning821 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 817 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 817 = false ∨ valuation q 821 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 818 = false ∨ valuationOf q 822 = true := by
  have hs : count819 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (818)) (literal (valuationOf q) (822)) (countLit q [-69, -71, -73]) (countLit q [-76, -78, -79]) (count819 q) 1 3 (meaning811 q) (meaning818 q) (meaning822 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 818 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 818 = false ∨ valuation q 822 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 820 = true := by
  have hs : count819 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -78, -79])
  have hm := merge_left (literal (valuationOf q) (812)) (literal (valuationOf q) (820)) (countLit q [-69, -71, -73]) (countLit q [-76, -78, -79]) (count819 q) 2 (meaning812 q) (meaning820 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 820 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 816 = false ∨ valuationOf q 821 = true := by
  have hs : count819 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (816)) (literal (valuationOf q) (821)) (countLit q [-69, -71, -73]) (countLit q [-76, -78, -79]) (count819 q) 2 1 (meaning812 q) (meaning816 q) (meaning821 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 816 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 816 = false ∨ valuation q 821 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 817 = false ∨ valuationOf q 822 = true := by
  have hs : count819 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (817)) (literal (valuationOf q) (822)) (countLit q [-69, -71, -73]) (countLit q [-76, -78, -79]) (count819 q) 2 2 (meaning812 q) (meaning817 q) (meaning822 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 817 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 817 = false ∨ valuation q 822 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 826 = true := by
  have hs : count825 q = (countLit q [-53, -58, -59, -62, -65, -67]) + (countLit q [-69, -71, -73, -76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67]) (l₂ := [-69, -71, -73, -76, -78, -79])
  have hm := merge_right (literal (valuationOf q) (820)) (literal (valuationOf q) (826)) (countLit q [-53, -58, -59, -62, -65, -67]) (countLit q [-69, -71, -73, -76, -78, -79]) (count825 q) 2 (meaning820 q) (meaning826 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 826 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 827 = true := by
  have hs : count825 q = (countLit q [-53, -58, -59, -62, -65, -67]) + (countLit q [-69, -71, -73, -76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67]) (l₂ := [-69, -71, -73, -76, -78, -79])
  have hm := merge_right (literal (valuationOf q) (821)) (literal (valuationOf q) (827)) (countLit q [-53, -58, -59, -62, -65, -67]) (countLit q [-69, -71, -73, -76, -78, -79]) (count825 q) 3 (meaning821 q) (meaning827 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 827 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 828 = true := by
  have hs : count825 q = (countLit q [-53, -58, -59, -62, -65, -67]) + (countLit q [-69, -71, -73, -76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67]) (l₂ := [-69, -71, -73, -76, -78, -79])
  have hm := merge_right (literal (valuationOf q) (822)) (literal (valuationOf q) (828)) (countLit q [-53, -58, -59, -62, -65, -67]) (countLit q [-69, -71, -73, -76, -78, -79]) (count825 q) 4 (meaning822 q) (meaning828 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 828 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 819 = false ∨ valuationOf q 826 = true := by
  have hs : count825 q = (countLit q [-53, -58, -59, -62, -65, -67]) + (countLit q [-69, -71, -73, -76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67]) (l₂ := [-69, -71, -73, -76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (819)) (literal (valuationOf q) (826)) (countLit q [-53, -58, -59, -62, -65, -67]) (countLit q [-69, -71, -73, -76, -78, -79]) (count825 q) 1 1 (meaning803 q) (meaning819 q) (meaning826 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 819 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 819 = false ∨ valuation q 826 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 820 = false ∨ valuationOf q 827 = true := by
  have hs : count825 q = (countLit q [-53, -58, -59, -62, -65, -67]) + (countLit q [-69, -71, -73, -76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67]) (l₂ := [-69, -71, -73, -76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (820)) (literal (valuationOf q) (827)) (countLit q [-53, -58, -59, -62, -65, -67]) (countLit q [-69, -71, -73, -76, -78, -79]) (count825 q) 1 2 (meaning803 q) (meaning820 q) (meaning827 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 820 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 820 = false ∨ valuation q 827 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 821 = false ∨ valuationOf q 828 = true := by
  have hs : count825 q = (countLit q [-53, -58, -59, -62, -65, -67]) + (countLit q [-69, -71, -73, -76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67]) (l₂ := [-69, -71, -73, -76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (821)) (literal (valuationOf q) (828)) (countLit q [-53, -58, -59, -62, -65, -67]) (countLit q [-69, -71, -73, -76, -78, -79]) (count825 q) 1 3 (meaning803 q) (meaning821 q) (meaning828 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 821 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 821 = false ∨ valuation q 828 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 822 = false ∨ valuationOf q 829 = true := by
  have hs : count825 q = (countLit q [-53, -58, -59, -62, -65, -67]) + (countLit q [-69, -71, -73, -76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67]) (l₂ := [-69, -71, -73, -76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (822)) (literal (valuationOf q) (829)) (countLit q [-53, -58, -59, -62, -65, -67]) (countLit q [-69, -71, -73, -76, -78, -79]) (count825 q) 1 4 (meaning803 q) (meaning822 q) (meaning829 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 822 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 822 = false ∨ valuation q 829 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 819 = false ∨ valuationOf q 827 = true := by
  have hs : count825 q = (countLit q [-53, -58, -59, -62, -65, -67]) + (countLit q [-69, -71, -73, -76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67]) (l₂ := [-69, -71, -73, -76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (819)) (literal (valuationOf q) (827)) (countLit q [-53, -58, -59, -62, -65, -67]) (countLit q [-69, -71, -73, -76, -78, -79]) (count825 q) 2 1 (meaning804 q) (meaning819 q) (meaning827 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 819 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 819 = false ∨ valuation q 827 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 820 = false ∨ valuationOf q 828 = true := by
  have hs : count825 q = (countLit q [-53, -58, -59, -62, -65, -67]) + (countLit q [-69, -71, -73, -76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67]) (l₂ := [-69, -71, -73, -76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (820)) (literal (valuationOf q) (828)) (countLit q [-53, -58, -59, -62, -65, -67]) (countLit q [-69, -71, -73, -76, -78, -79]) (count825 q) 2 2 (meaning804 q) (meaning820 q) (meaning828 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 820 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 820 = false ∨ valuation q 828 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 821 = false ∨ valuationOf q 829 = true := by
  have hs : count825 q = (countLit q [-53, -58, -59, -62, -65, -67]) + (countLit q [-69, -71, -73, -76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67]) (l₂ := [-69, -71, -73, -76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (821)) (literal (valuationOf q) (829)) (countLit q [-53, -58, -59, -62, -65, -67]) (countLit q [-69, -71, -73, -76, -78, -79]) (count825 q) 2 3 (meaning804 q) (meaning821 q) (meaning829 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 821 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 821 = false ∨ valuation q 829 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 820 = false ∨ valuationOf q 829 = true := by
  have hs : count825 q = (countLit q [-53, -58, -59, -62, -65, -67]) + (countLit q [-69, -71, -73, -76, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67]) (l₂ := [-69, -71, -73, -76, -78, -79])
  have hm := merge_two (literal (valuationOf q) (805)) (literal (valuationOf q) (820)) (literal (valuationOf q) (829)) (countLit q [-53, -58, -59, -62, -65, -67]) (countLit q [-69, -71, -73, -76, -78, -79]) (count825 q) 3 2 (meaning805 q) (meaning820 q) (meaning829 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 820 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 820 = false ∨ valuation q 829 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 835 = true := by
  have hs : count835 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (835)) (countLit q [-82]) (countLit q [-84]) (count835 q) 1 (meaningNeg84 q) (meaning835 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 835 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E075.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112075
