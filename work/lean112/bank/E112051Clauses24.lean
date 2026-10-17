import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 993 = false ∨ valuationOf q 999 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (993)) (literal (valuationOf q) (999)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 2 2 (meaning985 q) (meaning993 q) (meaning999 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 993 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 993 = false ∨ valuation q 999 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 998 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_left (literal (valuationOf q) (986)) (literal (valuationOf q) (998)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 3 (meaning986 q) (meaning998 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 998 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 992 = false ∨ valuationOf q 999 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (986)) (literal (valuationOf q) (992)) (literal (valuationOf q) (999)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 3 1 (meaning986 q) (meaning992 q) (meaning999 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 992 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 992 = false ∨ valuation q 999 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 993 = false ∨ valuationOf q 1000 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (986)) (literal (valuationOf q) (993)) (literal (valuationOf q) (1000)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 3 2 (meaning986 q) (meaning993 q) (meaning1000 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 993 = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 993 = false ∨ valuation q 1000 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 987 = false ∨ valuationOf q 999 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_left (literal (valuationOf q) (987)) (literal (valuationOf q) (999)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 4 (meaning987 q) (meaning999 q) hs
  change valuationOf q 987 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 987 = false ∨ valuation q 999 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 987 = false ∨ valuationOf q 992 = false ∨ valuationOf q 1000 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (987)) (literal (valuationOf q) (992)) (literal (valuationOf q) (1000)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 4 1 (meaning987 q) (meaning992 q) (meaning1000 q) hs
  change valuationOf q 987 = false ∨ valuationOf q 992 = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 987 = false ∨ valuation q 992 = false ∨ valuation q 1000 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1007 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1007)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 1 3 (meaning973 q) (meaning998 q) (meaning1007 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 998 = false ∨ valuation q 1007 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1008 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1008)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 1 4 (meaning973 q) (meaning999 q) (meaning1008 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 999 = false ∨ valuation q 1008 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1009 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1000)) (literal (valuationOf q) (1009)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 1 5 (meaning973 q) (meaning1000 q) (meaning1009 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1000 = false ∨ valuation q 1009 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1007 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1007)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 2 2 (meaning974 q) (meaning997 q) (meaning1007 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 997 = false ∨ valuation q 1007 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1008 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1008)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 2 3 (meaning974 q) (meaning998 q) (meaning1008 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 998 = false ∨ valuation q 1008 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1009 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1009)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 2 4 (meaning974 q) (meaning999 q) (meaning1009 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 999 = false ∨ valuation q 1009 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1007 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (996)) (literal (valuationOf q) (1007)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 3 1 (meaning975 q) (meaning996 q) (meaning1007 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 996 = false ∨ valuation q 1007 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1008 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1008)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 3 2 (meaning975 q) (meaning997 q) (meaning1008 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 997 = false ∨ valuation q 1008 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1009 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1009)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 3 3 (meaning975 q) (meaning998 q) (meaning1009 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 998 = false ∨ valuation q 1009 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1008 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (996)) (literal (valuationOf q) (1008)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 4 1 (meaning976 q) (meaning996 q) (meaning1008 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 996 = false ∨ valuation q 1008 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1009 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1009)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 4 2 (meaning976 q) (meaning997 q) (meaning1009 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 997 = false ∨ valuation q 1009 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1010 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1010)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 4 3 (meaning976 q) (meaning998 q) (meaning1010 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 998 = false ∨ valuation q 1010 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1008 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_left (literal (valuationOf q) (977)) (literal (valuationOf q) (1008)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 5 (meaning977 q) (meaning1008 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1008 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1009 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (996)) (literal (valuationOf q) (1009)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 5 1 (meaning977 q) (meaning996 q) (meaning1009 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 996 = false ∨ valuation q 1009 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1010 = true := by
  have hs : count1004 q = (countLit q [-85, -86, -90, -91, -93, -95, -97]) + (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90, -91, -93, -95, -97]) (l₂ := [-99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1010)) (countLit q [-85, -86, -90, -91, -93, -95, -97]) (countLit q [-99, -101, -103, -108, -111, -112, -113, -114]) (count1004 q) 5 2 (meaning977 q) (meaning997 q) (meaning1010 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 997 = false ∨ valuation q 1010 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1026 = true := by
  have hs : count1019 q = (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) + (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (l₂ := [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (1007)) (literal (valuationOf q) (1026)) (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) (count1019 q) 4 4 (meaning949 q) (meaning1007 q) (meaning1026 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 1007 = false ∨ valuation q 1026 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1028 = true := by
  have hs : count1019 q = (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) + (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (l₂ := [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (1009)) (literal (valuationOf q) (1028)) (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) (count1019 q) 4 6 (meaning949 q) (meaning1009 q) (meaning1028 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 1009 = false ∨ valuation q 1028 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1029 = true := by
  have hs : count1019 q = (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) + (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (l₂ := [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1029)) (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) (count1019 q) 4 7 (meaning949 q) (meaning1010 q) (meaning1029 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 1010 = false ∨ valuation q 1029 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1028 = true := by
  have hs : count1019 q = (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) + (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (l₂ := [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (1008)) (literal (valuationOf q) (1028)) (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) (count1019 q) 5 5 (meaning950 q) (meaning1008 q) (meaning1028 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 1008 = false ∨ valuation q 1028 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1029 = true := by
  have hs : count1019 q = (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) + (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (l₂ := [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (1009)) (literal (valuationOf q) (1029)) (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) (count1019 q) 5 6 (meaning950 q) (meaning1009 q) (meaning1029 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 1009 = false ∨ valuation q 1029 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1028 = true := by
  have hs : count1019 q = (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) + (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (l₂ := [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (951)) (literal (valuationOf q) (1007)) (literal (valuationOf q) (1028)) (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) (count1019 q) 6 4 (meaning951 q) (meaning1007 q) (meaning1028 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 1007 = false ∨ valuation q 1028 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1029 = true := by
  have hs : count1019 q = (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) + (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (l₂ := [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (951)) (literal (valuationOf q) (1008)) (literal (valuationOf q) (1029)) (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) (count1019 q) 6 5 (meaning951 q) (meaning1008 q) (meaning1029 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 1008 = false ∨ valuation q 1029 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1029 = true := by
  have hs : count1019 q = (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) + (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (l₂ := [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (952)) (literal (valuationOf q) (1007)) (literal (valuationOf q) (1029)) (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]) (countLit q [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) (count1019 q) 7 4 (meaning952 q) (meaning1007 q) (meaning1029 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 1007 = false ∨ valuation q 1029 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1052 = true := by
  have hs : count1036 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30, -31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) + (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81, -85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30, -31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (l₂ := [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81, -85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1052)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30, -31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81, -85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) (count1036 q) 6 11 (meaning894 q) (meaning1029 q) (meaning1052 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 1029 = false ∨ valuation q 1052 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1052 = true := by
  have hs : count1036 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30, -31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) + (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81, -85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30, -31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (l₂ := [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81, -85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1052)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30, -31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81, -85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) (count1036 q) 7 10 (meaning895 q) (meaning1028 q) (meaning1052 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 1028 = false ∨ valuation q 1052 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1052 = true := by
  have hs : count1036 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30, -31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) + (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81, -85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30, -31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (l₂ := [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81, -85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1052)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30, -31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (countLit q [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81, -85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]) (count1036 q) 9 8 (meaning897 q) (meaning1026 q) (meaning1052 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 1026 = false ∨ valuation q 1052 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E051.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112051
