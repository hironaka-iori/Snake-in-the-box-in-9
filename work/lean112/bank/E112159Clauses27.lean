import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 993 = false ∨ valuationOf q 996 = true := by
  have hs : count994 q = (countLit q [-88]) + (countLit q [-90, -94]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -94])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (993)) (literal (valuationOf q) (996)) (countLit q [-88]) (countLit q [-90, -94]) (count994 q) 1 2 (meaningNeg88 q) (meaning993 q) (meaning996 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 993 = false ∨ valuationOf q 996 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 993 = false ∨ valuation q 996 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 997 = true := by
  have hs : count997 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (997)) (countLit q [-95]) (countLit q [-98]) (count997 q) 1 (meaningNeg98 q) (meaning997 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 997 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 997 = true := by
  have hs : count997 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (997)) (countLit q [-95]) (countLit q [-98]) (count997 q) 1 (meaningNeg95 q) (meaning997 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 997 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 98 = true ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (998)) (countLit q [-95]) (countLit q [-98]) (count997 q) 1 1 (meaningNeg95 q) (meaningNeg98 q) (meaning998 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 98 = true ∨ valuation q 998 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 999 = true := by
  have hs : count999 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (999)) (countLit q [-99]) (countLit q [-101]) (count999 q) 1 (meaningNeg101 q) (meaning999 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 999 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 999 = true := by
  have hs : count999 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (999)) (countLit q [-99]) (countLit q [-101]) (count999 q) 1 (meaningNeg99 q) (meaning999 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 999 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1000 = true := by
  have hs : count999 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1000)) (countLit q [-99]) (countLit q [-101]) (count999 q) 1 1 (meaningNeg99 q) (meaningNeg101 q) (meaning1000 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 101 = true ∨ valuation q 1000 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (999)) (literal (valuationOf q) (1001)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1001 q) 1 (meaning999 q) (meaning1001 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1001 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (1000)) (literal (valuationOf q) (1002)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1001 q) 2 (meaning1000 q) (meaning1002 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1002 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_left (literal (valuationOf q) (997)) (literal (valuationOf q) (1001)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1001 q) 1 (meaning997 q) (meaning1001 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1001 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (997)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1002)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1001 q) 1 1 (meaning997 q) (meaning999 q) (meaning1002 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 999 = false ∨ valuation q 1002 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (997)) (literal (valuationOf q) (1000)) (literal (valuationOf q) (1003)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1001 q) 1 2 (meaning997 q) (meaning1000 q) (meaning1003 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1000 = false ∨ valuation q 1003 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_left (literal (valuationOf q) (998)) (literal (valuationOf q) (1002)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1001 q) 2 (meaning998 q) (meaning1002 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 1002 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (998)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1003)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1001 q) 2 1 (meaning998 q) (meaning999 q) (meaning1003 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 999 = false ∨ valuation q 1003 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1005 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_right (literal (valuationOf q) (1001)) (literal (valuationOf q) (1005)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 1 (meaning1001 q) (meaning1005 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1005 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1006 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_right (literal (valuationOf q) (1002)) (literal (valuationOf q) (1006)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 2 (meaning1002 q) (meaning1006 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1006 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1007 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_right (literal (valuationOf q) (1003)) (literal (valuationOf q) (1007)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 3 (meaning1003 q) (meaning1007 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1007 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 1005 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_left (literal (valuationOf q) (994)) (literal (valuationOf q) (1005)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 1 (meaning994 q) (meaning1005 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 1005 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 1001 = false ∨ valuationOf q 1006 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (1001)) (literal (valuationOf q) (1006)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 1 1 (meaning994 q) (meaning1001 q) (meaning1006 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 1001 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 1001 = false ∨ valuation q 1006 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1007 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (1002)) (literal (valuationOf q) (1007)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 1 2 (meaning994 q) (meaning1002 q) (meaning1007 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 1002 = false ∨ valuation q 1007 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 1003 = false ∨ valuationOf q 1008 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (1003)) (literal (valuationOf q) (1008)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 1 3 (meaning994 q) (meaning1003 q) (meaning1008 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 1003 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 1003 = false ∨ valuation q 1008 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 995 = false ∨ valuationOf q 1006 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_left (literal (valuationOf q) (995)) (literal (valuationOf q) (1006)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 2 (meaning995 q) (meaning1006 q) hs
  change valuationOf q 995 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 995 = false ∨ valuation q 1006 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 995 = false ∨ valuationOf q 1001 = false ∨ valuationOf q 1007 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (995)) (literal (valuationOf q) (1001)) (literal (valuationOf q) (1007)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 2 1 (meaning995 q) (meaning1001 q) (meaning1007 q) hs
  change valuationOf q 995 = false ∨ valuationOf q 1001 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 995 = false ∨ valuation q 1001 = false ∨ valuation q 1007 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 995 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1008 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (995)) (literal (valuationOf q) (1002)) (literal (valuationOf q) (1008)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 2 2 (meaning995 q) (meaning1002 q) (meaning1008 q) hs
  change valuationOf q 995 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 995 = false ∨ valuation q 1002 = false ∨ valuation q 1008 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1007 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_left (literal (valuationOf q) (996)) (literal (valuationOf q) (1007)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 3 (meaning996 q) (meaning1007 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1007 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1001 = false ∨ valuationOf q 1008 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (996)) (literal (valuationOf q) (1001)) (literal (valuationOf q) (1008)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 3 1 (meaning996 q) (meaning1001 q) (meaning1008 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1001 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1001 = false ∨ valuation q 1008 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1009 = true := by
  have hs : count1005 q = (countLit q [-88, -90, -94]) + (countLit q [-95, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -94]) (l₂ := [-95, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (996)) (literal (valuationOf q) (1002)) (literal (valuationOf q) (1009)) (countLit q [-88, -90, -94]) (countLit q [-95, -98, -99, -101]) (count1005 q) 3 2 (meaning996 q) (meaning1002 q) (meaning1009 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1002 = false ∨ valuation q 1009 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1012)) (countLit q [-104]) (countLit q [-105]) (count1012 q) 1 (meaningNeg105 q) (meaning1012 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1012 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1012)) (countLit q [-104]) (countLit q [-105]) (count1012 q) 1 (meaningNeg104 q) (meaning1012 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1012 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1013)) (countLit q [-104]) (countLit q [-105]) (count1012 q) 1 1 (meaningNeg104 q) (meaningNeg105 q) (meaning1013 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 105 = true ∨ valuation q 1013 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1014 = true := by
  have hs : count1014 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1014)) (countLit q [-106]) (countLit q [-108]) (count1014 q) 1 (meaningNeg108 q) (meaning1014 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1014 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1014 = true := by
  have hs : count1014 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1014)) (countLit q [-106]) (countLit q [-108]) (count1014 q) 1 (meaningNeg106 q) (meaning1014 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1014 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E159.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112159
