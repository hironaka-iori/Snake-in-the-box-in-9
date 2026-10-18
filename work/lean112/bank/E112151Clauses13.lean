import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 844 = true := by
  have hs : count844 q = (countLit q [-58]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (844)) (countLit q [-58]) (countLit q [-59]) (count844 q) 1 (meaningNeg59 q) (meaning844 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 844 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 844 = true := by
  have hs : count844 q = (countLit q [-58]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (844)) (countLit q [-58]) (countLit q [-59]) (count844 q) 1 (meaningNeg58 q) (meaning844 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 844 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 846 = true := by
  have hs : count846 q = (countLit q [-56]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58, -59])
  have hm := merge_right (literal (valuationOf q) (844)) (literal (valuationOf q) (846)) (countLit q [-56]) (countLit q [-58, -59]) (count846 q) 1 (meaning844 q) (meaning846 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 846 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 846 = true := by
  have hs : count846 q = (countLit q [-56]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58, -59])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (846)) (countLit q [-56]) (countLit q [-58, -59]) (count846 q) 1 (meaningNeg56 q) (meaning846 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 846 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 844 = false ∨ valuationOf q 847 = true := by
  have hs : count846 q = (countLit q [-56]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58, -59])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (844)) (literal (valuationOf q) (847)) (countLit q [-56]) (countLit q [-58, -59]) (count846 q) 1 1 (meaningNeg56 q) (meaning844 q) (meaning847 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 844 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 844 = false ∨ valuation q 847 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 849 = true := by
  have hs : count849 q = (countLit q [-63]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (849)) (countLit q [-63]) (countLit q [-64]) (count849 q) 1 (meaningNeg64 q) (meaning849 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 849 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 849 = true := by
  have hs : count849 q = (countLit q [-63]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (849)) (countLit q [-63]) (countLit q [-64]) (count849 q) 1 (meaningNeg63 q) (meaning849 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 849 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 64 = true ∨ valuationOf q 850 = true := by
  have hs : count849 q = (countLit q [-63]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (-64)) (literal (valuationOf q) (850)) (countLit q [-63]) (countLit q [-64]) (count849 q) 1 1 (meaningNeg63 q) (meaningNeg64 q) (meaning850 q) hs
  change (! (valuationOf q 63)) = false ∨ (! (valuationOf q 64)) = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 64 = true ∨ valuation q 850 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 851 = true := by
  have hs : count851 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_right (literal (valuationOf q) (849)) (literal (valuationOf q) (851)) (countLit q [-62]) (countLit q [-63, -64]) (count851 q) 1 (meaning849 q) (meaning851 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 851 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 852 = true := by
  have hs : count851 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_right (literal (valuationOf q) (850)) (literal (valuationOf q) (852)) (countLit q [-62]) (countLit q [-63, -64]) (count851 q) 2 (meaning850 q) (meaning852 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 852 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 849 = false ∨ valuationOf q 852 = true := by
  have hs : count851 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (849)) (literal (valuationOf q) (852)) (countLit q [-62]) (countLit q [-63, -64]) (count851 q) 1 1 (meaningNeg62 q) (meaning849 q) (meaning852 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 849 = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 849 = false ∨ valuation q 852 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 854 = true := by
  have hs : count854 q = (countLit q [-56, -58, -59]) + (countLit q [-62, -63, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59]) (l₂ := [-62, -63, -64])
  have hm := merge_right (literal (valuationOf q) (851)) (literal (valuationOf q) (854)) (countLit q [-56, -58, -59]) (countLit q [-62, -63, -64]) (count854 q) 1 (meaning851 q) (meaning854 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 854 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 855 = true := by
  have hs : count854 q = (countLit q [-56, -58, -59]) + (countLit q [-62, -63, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59]) (l₂ := [-62, -63, -64])
  have hm := merge_right (literal (valuationOf q) (852)) (literal (valuationOf q) (855)) (countLit q [-56, -58, -59]) (countLit q [-62, -63, -64]) (count854 q) 2 (meaning852 q) (meaning855 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 855 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 854 = true := by
  have hs : count854 q = (countLit q [-56, -58, -59]) + (countLit q [-62, -63, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59]) (l₂ := [-62, -63, -64])
  have hm := merge_left (literal (valuationOf q) (846)) (literal (valuationOf q) (854)) (countLit q [-56, -58, -59]) (countLit q [-62, -63, -64]) (count854 q) 1 (meaning846 q) (meaning854 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 854 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 851 = false ∨ valuationOf q 855 = true := by
  have hs : count854 q = (countLit q [-56, -58, -59]) + (countLit q [-62, -63, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59]) (l₂ := [-62, -63, -64])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (851)) (literal (valuationOf q) (855)) (countLit q [-56, -58, -59]) (countLit q [-62, -63, -64]) (count854 q) 1 1 (meaning846 q) (meaning851 q) (meaning855 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 851 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 851 = false ∨ valuation q 855 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 852 = false ∨ valuationOf q 856 = true := by
  have hs : count854 q = (countLit q [-56, -58, -59]) + (countLit q [-62, -63, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59]) (l₂ := [-62, -63, -64])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (852)) (literal (valuationOf q) (856)) (countLit q [-56, -58, -59]) (countLit q [-62, -63, -64]) (count854 q) 1 2 (meaning846 q) (meaning852 q) (meaning856 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 852 = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 852 = false ∨ valuation q 856 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 855 = true := by
  have hs : count854 q = (countLit q [-56, -58, -59]) + (countLit q [-62, -63, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59]) (l₂ := [-62, -63, -64])
  have hm := merge_left (literal (valuationOf q) (847)) (literal (valuationOf q) (855)) (countLit q [-56, -58, -59]) (countLit q [-62, -63, -64]) (count854 q) 2 (meaning847 q) (meaning855 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 855 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 851 = false ∨ valuationOf q 856 = true := by
  have hs : count854 q = (countLit q [-56, -58, -59]) + (countLit q [-62, -63, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59]) (l₂ := [-62, -63, -64])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (851)) (literal (valuationOf q) (856)) (countLit q [-56, -58, -59]) (countLit q [-62, -63, -64]) (count854 q) 2 1 (meaning847 q) (meaning851 q) (meaning856 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 851 = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 851 = false ∨ valuation q 856 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (860)) (countLit q [-70]) (countLit q [-72]) (count860 q) 1 (meaningNeg72 q) (meaning860 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 860 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (860)) (countLit q [-70]) (countLit q [-72]) (count860 q) 1 (meaningNeg70 q) (meaning860 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 860 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 862 = true := by
  have hs : count862 q = (countLit q [-67]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70, -72])
  have hm := merge_right (literal (valuationOf q) (860)) (literal (valuationOf q) (862)) (countLit q [-67]) (countLit q [-70, -72]) (count862 q) 1 (meaning860 q) (meaning862 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 862 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 862 = true := by
  have hs : count862 q = (countLit q [-67]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70, -72])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (862)) (countLit q [-67]) (countLit q [-70, -72]) (count862 q) 1 (meaningNeg67 q) (meaning862 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 862 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 860 = false ∨ valuationOf q 863 = true := by
  have hs : count862 q = (countLit q [-67]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (860)) (literal (valuationOf q) (863)) (countLit q [-67]) (countLit q [-70, -72]) (count862 q) 1 1 (meaningNeg67 q) (meaning860 q) (meaning863 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 860 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 860 = false ∨ valuation q 863 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_right (literal (valuationOf q) (-75)) (literal (valuationOf q) (865)) (countLit q [-74]) (countLit q [-75]) (count865 q) 1 (meaningNeg75 q) (meaning865 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 865 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (865)) (countLit q [-74]) (countLit q [-75]) (count865 q) 1 (meaningNeg74 q) (meaning865 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 865 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 75 = true ∨ valuationOf q 866 = true := by
  have hs : count865 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-75)) (literal (valuationOf q) (866)) (countLit q [-74]) (countLit q [-75]) (count865 q) 1 1 (meaningNeg74 q) (meaningNeg75 q) (meaning866 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 75)) = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 75 = true ∨ valuation q 866 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 867 = true := by
  have hs : count867 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (867)) (countLit q [-76]) (countLit q [-79]) (count867 q) 1 (meaningNeg79 q) (meaning867 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 867 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 867 = true := by
  have hs : count867 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (867)) (countLit q [-76]) (countLit q [-79]) (count867 q) 1 (meaningNeg76 q) (meaning867 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 867 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 79 = true ∨ valuationOf q 868 = true := by
  have hs : count867 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (868)) (countLit q [-76]) (countLit q [-79]) (count867 q) 1 1 (meaningNeg76 q) (meaningNeg79 q) (meaning868 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 79 = true ∨ valuation q 868 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-74, -75]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-76, -79])
  have hm := merge_right (literal (valuationOf q) (867)) (literal (valuationOf q) (869)) (countLit q [-74, -75]) (countLit q [-76, -79]) (count869 q) 1 (meaning867 q) (meaning869 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 869 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-74, -75]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-76, -79])
  have hm := merge_right (literal (valuationOf q) (868)) (literal (valuationOf q) (870)) (countLit q [-74, -75]) (countLit q [-76, -79]) (count869 q) 2 (meaning868 q) (meaning870 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 870 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-74, -75]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-76, -79])
  have hm := merge_left (literal (valuationOf q) (865)) (literal (valuationOf q) (869)) (countLit q [-74, -75]) (countLit q [-76, -79]) (count869 q) 1 (meaning865 q) (meaning869 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 869 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E151.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112151
