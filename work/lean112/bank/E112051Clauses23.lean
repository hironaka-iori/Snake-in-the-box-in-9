import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 964 = false ∨ valuationOf q 969 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (964)) (literal (valuationOf q) (969)) (literal (valuationOf q) (976)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 3 1 (meaning964 q) (meaning969 q) (meaning976 q) hs
  change valuationOf q 964 = false ∨ valuationOf q 969 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 964 = false ∨ valuation q 969 = false ∨ valuation q 976 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 964 = false ∨ valuationOf q 970 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (964)) (literal (valuationOf q) (970)) (literal (valuationOf q) (977)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 3 2 (meaning964 q) (meaning970 q) (meaning977 q) hs
  change valuationOf q 964 = false ∨ valuationOf q 970 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 964 = false ∨ valuation q 970 = false ∨ valuation q 977 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 980 = true := by
  have hs : count980 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (980)) (countLit q [-99]) (countLit q [-101]) (count980 q) 1 (meaningNeg101 q) (meaning980 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 980 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 980 = true := by
  have hs : count980 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (980)) (countLit q [-99]) (countLit q [-101]) (count980 q) 1 (meaningNeg99 q) (meaning980 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 980 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 101 = true ∨ valuationOf q 981 = true := by
  have hs : count980 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (981)) (countLit q [-99]) (countLit q [-101]) (count980 q) 1 1 (meaningNeg99 q) (meaningNeg101 q) (meaning981 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 101 = true ∨ valuation q 981 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 982 = true := by
  have hs : count982 q = (countLit q [-103]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (982)) (countLit q [-103]) (countLit q [-108]) (count982 q) 1 (meaningNeg108 q) (meaning982 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 982 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 982 = true := by
  have hs : count982 q = (countLit q [-103]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (982)) (countLit q [-103]) (countLit q [-108]) (count982 q) 1 (meaningNeg103 q) (meaning982 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 982 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 108 = true ∨ valuationOf q 983 = true := by
  have hs : count982 q = (countLit q [-103]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (983)) (countLit q [-103]) (countLit q [-108]) (count982 q) 1 1 (meaningNeg103 q) (meaningNeg108 q) (meaning983 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 108 = true ∨ valuation q 983 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 982 = false ∨ valuationOf q 984 = true := by
  have hs : count984 q = (countLit q [-99, -101]) + (countLit q [-103, -108]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-103, -108])
  have hm := merge_right (literal (valuationOf q) (982)) (literal (valuationOf q) (984)) (countLit q [-99, -101]) (countLit q [-103, -108]) (count984 q) 1 (meaning982 q) (meaning984 q) hs
  change valuationOf q 982 = false ∨ valuationOf q 984 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 982 = false ∨ valuation q 984 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 984 = true := by
  have hs : count984 q = (countLit q [-99, -101]) + (countLit q [-103, -108]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-103, -108])
  have hm := merge_left (literal (valuationOf q) (980)) (literal (valuationOf q) (984)) (countLit q [-99, -101]) (countLit q [-103, -108]) (count984 q) 1 (meaning980 q) (meaning984 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 984 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 984 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 982 = false ∨ valuationOf q 985 = true := by
  have hs : count984 q = (countLit q [-99, -101]) + (countLit q [-103, -108]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-103, -108])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (982)) (literal (valuationOf q) (985)) (countLit q [-99, -101]) (countLit q [-103, -108]) (count984 q) 1 1 (meaning980 q) (meaning982 q) (meaning985 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 982 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 982 = false ∨ valuation q 985 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 983 = false ∨ valuationOf q 986 = true := by
  have hs : count984 q = (countLit q [-99, -101]) + (countLit q [-103, -108]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-103, -108])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (983)) (literal (valuationOf q) (986)) (countLit q [-99, -101]) (countLit q [-103, -108]) (count984 q) 1 2 (meaning980 q) (meaning983 q) (meaning986 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 983 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 983 = false ∨ valuation q 986 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 985 = true := by
  have hs : count984 q = (countLit q [-99, -101]) + (countLit q [-103, -108]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-103, -108])
  have hm := merge_left (literal (valuationOf q) (981)) (literal (valuationOf q) (985)) (countLit q [-99, -101]) (countLit q [-103, -108]) (count984 q) 2 (meaning981 q) (meaning985 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 985 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 982 = false ∨ valuationOf q 986 = true := by
  have hs : count984 q = (countLit q [-99, -101]) + (countLit q [-103, -108]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-103, -108])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (982)) (literal (valuationOf q) (986)) (countLit q [-99, -101]) (countLit q [-103, -108]) (count984 q) 2 1 (meaning981 q) (meaning982 q) (meaning986 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 982 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 982 = false ∨ valuation q 986 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 983 = false ∨ valuationOf q 987 = true := by
  have hs : count984 q = (countLit q [-99, -101]) + (countLit q [-103, -108]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-103, -108])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (983)) (literal (valuationOf q) (987)) (countLit q [-99, -101]) (countLit q [-103, -108]) (count984 q) 2 2 (meaning981 q) (meaning983 q) (meaning987 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 983 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 983 = false ∨ valuation q 987 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_right (literal (valuationOf q) (-112)) (literal (valuationOf q) (988)) (countLit q [-111]) (countLit q [-112]) (count988 q) 1 (meaningNeg112 q) (meaning988 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 988 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (988)) (countLit q [-111]) (countLit q [-112]) (count988 q) 1 (meaningNeg111 q) (meaning988 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 988 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 112 = true ∨ valuationOf q 989 = true := by
  have hs : count988 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-112)) (literal (valuationOf q) (989)) (countLit q [-111]) (countLit q [-112]) (count988 q) 1 1 (meaningNeg111 q) (meaningNeg112 q) (meaning989 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 112)) = false ∨ valuationOf q 989 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 989 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (990)) (countLit q [-113]) (countLit q [-114]) (count990 q) 1 (meaningNeg114 q) (meaning990 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 990 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 992 = true := by
  have hs : count992 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_right (literal (valuationOf q) (990)) (literal (valuationOf q) (992)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count992 q) 1 (meaning990 q) (meaning992 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 992 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 992 = true := by
  have hs : count992 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_left (literal (valuationOf q) (988)) (literal (valuationOf q) (992)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count992 q) 1 (meaning988 q) (meaning992 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 992 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 990 = false ∨ valuationOf q 993 = true := by
  have hs : count992 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (988)) (literal (valuationOf q) (990)) (literal (valuationOf q) (993)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count992 q) 1 1 (meaning988 q) (meaning990 q) (meaning993 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 990 = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 990 = false ∨ valuation q 993 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 989 = false ∨ valuationOf q 993 = true := by
  have hs : count992 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_left (literal (valuationOf q) (989)) (literal (valuationOf q) (993)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count992 q) 2 (meaning989 q) (meaning993 q) hs
  change valuationOf q 989 = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 989 = false ∨ valuation q 993 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 989 = false ∨ valuationOf q 990 = false ∨ valuationOf q 994 = true := by
  have hs : count992 q = (countLit q [-111, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (989)) (literal (valuationOf q) (990)) (literal (valuationOf q) (994)) (countLit q [-111, -112]) (countLit q [-113, -114]) (count992 q) 2 1 (meaning989 q) (meaning990 q) (meaning994 q) hs
  change valuationOf q 989 = false ∨ valuationOf q 990 = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 989 = false ∨ valuation q 990 = false ∨ valuation q 994 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 996 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_right (literal (valuationOf q) (992)) (literal (valuationOf q) (996)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 1 (meaning992 q) (meaning996 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 996 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 996 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 997 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_right (literal (valuationOf q) (993)) (literal (valuationOf q) (997)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 2 (meaning993 q) (meaning997 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 997 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 984 = false ∨ valuationOf q 996 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_left (literal (valuationOf q) (984)) (literal (valuationOf q) (996)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 1 (meaning984 q) (meaning996 q) hs
  change valuationOf q 984 = false ∨ valuationOf q 996 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 984 = false ∨ valuation q 996 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 984 = false ∨ valuationOf q 992 = false ∨ valuationOf q 997 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (984)) (literal (valuationOf q) (992)) (literal (valuationOf q) (997)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 1 1 (meaning984 q) (meaning992 q) (meaning997 q) hs
  change valuationOf q 984 = false ∨ valuationOf q 992 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 984 = false ∨ valuation q 992 = false ∨ valuation q 997 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 984 = false ∨ valuationOf q 993 = false ∨ valuationOf q 998 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (984)) (literal (valuationOf q) (993)) (literal (valuationOf q) (998)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 1 2 (meaning984 q) (meaning993 q) (meaning998 q) hs
  change valuationOf q 984 = false ∨ valuationOf q 993 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 984 = false ∨ valuation q 993 = false ∨ valuation q 998 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 984 = false ∨ valuationOf q 994 = false ∨ valuationOf q 999 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (984)) (literal (valuationOf q) (994)) (literal (valuationOf q) (999)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 1 3 (meaning984 q) (meaning994 q) (meaning999 q) hs
  change valuationOf q 984 = false ∨ valuationOf q 994 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 984 = false ∨ valuation q 994 = false ∨ valuation q 999 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 997 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_left (literal (valuationOf q) (985)) (literal (valuationOf q) (997)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 2 (meaning985 q) (meaning997 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 997 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 992 = false ∨ valuationOf q 998 = true := by
  have hs : count996 q = (countLit q [-99, -101, -103, -108]) + (countLit q [-111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-99, -101, -103, -108]) (l₂ := [-111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (992)) (literal (valuationOf q) (998)) (countLit q [-99, -101, -103, -108]) (countLit q [-111, -112, -113, -114]) (count996 q) 2 1 (meaning985 q) (meaning992 q) (meaning998 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 992 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 992 = false ∨ valuation q 998 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E051.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112051
