import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 979 = false ∨ valuationOf q 983 = true := by
  have hs : count981 q = (countLit q [-69, -70]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-72, -74])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (979)) (literal (valuationOf q) (983)) (countLit q [-69, -70]) (countLit q [-72, -74]) (count981 q) 2 1 (meaning978 q) (meaning979 q) (meaning983 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 979 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 979 = false ∨ valuation q 983 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 985 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_right (literal (valuationOf q) (981)) (literal (valuationOf q) (985)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 1 (meaning981 q) (meaning985 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 985 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 982 = false ∨ valuationOf q 986 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_right (literal (valuationOf q) (982)) (literal (valuationOf q) (986)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 2 (meaning982 q) (meaning986 q) hs
  change valuationOf q 982 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 982 = false ∨ valuation q 986 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 983 = false ∨ valuationOf q 987 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_right (literal (valuationOf q) (983)) (literal (valuationOf q) (987)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 3 (meaning983 q) (meaning987 q) hs
  change valuationOf q 983 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 983 = false ∨ valuation q 987 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 985 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_left (literal (valuationOf q) (974)) (literal (valuationOf q) (985)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 1 (meaning974 q) (meaning985 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 985 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 981 = false ∨ valuationOf q 986 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (981)) (literal (valuationOf q) (986)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 1 1 (meaning974 q) (meaning981 q) (meaning986 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 981 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 981 = false ∨ valuation q 986 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 982 = false ∨ valuationOf q 987 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (982)) (literal (valuationOf q) (987)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 1 2 (meaning974 q) (meaning982 q) (meaning987 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 982 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 982 = false ∨ valuation q 987 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 983 = false ∨ valuationOf q 988 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (983)) (literal (valuationOf q) (988)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 1 3 (meaning974 q) (meaning983 q) (meaning988 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 983 = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 983 = false ∨ valuation q 988 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 986 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_left (literal (valuationOf q) (975)) (literal (valuationOf q) (986)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 2 (meaning975 q) (meaning986 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 986 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 981 = false ∨ valuationOf q 987 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (981)) (literal (valuationOf q) (987)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 2 1 (meaning975 q) (meaning981 q) (meaning987 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 981 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 981 = false ∨ valuation q 987 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 982 = false ∨ valuationOf q 988 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (982)) (literal (valuationOf q) (988)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 2 2 (meaning975 q) (meaning982 q) (meaning988 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 982 = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 982 = false ∨ valuation q 988 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 983 = false ∨ valuationOf q 989 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (983)) (literal (valuationOf q) (989)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 2 3 (meaning975 q) (meaning983 q) (meaning989 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 983 = false ∨ valuationOf q 989 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 983 = false ∨ valuation q 989 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 987 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_left (literal (valuationOf q) (976)) (literal (valuationOf q) (987)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 3 (meaning976 q) (meaning987 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 987 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 981 = false ∨ valuationOf q 988 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (981)) (literal (valuationOf q) (988)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 3 1 (meaning976 q) (meaning981 q) (meaning988 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 981 = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 981 = false ∨ valuation q 988 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 982 = false ∨ valuationOf q 989 = true := by
  have hs : count985 q = (countLit q [-61, -64, -65]) + (countLit q [-69, -70, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-69, -70, -72, -74])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (982)) (literal (valuationOf q) (989)) (countLit q [-61, -64, -65]) (countLit q [-69, -70, -72, -74]) (count985 q) 3 2 (meaning976 q) (meaning982 q) (meaning989 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 982 = false ∨ valuationOf q 989 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 982 = false ∨ valuation q 989 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 992 = true := by
  have hs : count992 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (992)) (countLit q [-76]) (countLit q [-79]) (count992 q) 1 (meaningNeg79 q) (meaning992 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 992 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 992 = true := by
  have hs : count992 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (992)) (countLit q [-76]) (countLit q [-79]) (count992 q) 1 (meaningNeg76 q) (meaning992 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 992 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 79 = true ∨ valuationOf q 993 = true := by
  have hs : count992 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (993)) (countLit q [-76]) (countLit q [-79]) (count992 q) 1 1 (meaningNeg76 q) (meaningNeg79 q) (meaning993 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 79 = true ∨ valuation q 993 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 994 = true := by
  have hs : count994 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (994)) (countLit q [-81]) (countLit q [-82]) (count994 q) 1 (meaningNeg82 q) (meaning994 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 994 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 994 = true := by
  have hs : count994 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (994)) (countLit q [-81]) (countLit q [-82]) (count994 q) 1 (meaningNeg81 q) (meaning994 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 994 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 82 = true ∨ valuationOf q 995 = true := by
  have hs : count994 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (995)) (countLit q [-81]) (countLit q [-82]) (count994 q) 1 1 (meaningNeg81 q) (meaningNeg82 q) (meaning995 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 995 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 996 = true := by
  have hs : count996 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_right (literal (valuationOf q) (994)) (literal (valuationOf q) (996)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count996 q) 1 (meaning994 q) (meaning996 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 996 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 996 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 995 = false ∨ valuationOf q 997 = true := by
  have hs : count996 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_right (literal (valuationOf q) (995)) (literal (valuationOf q) (997)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count996 q) 2 (meaning995 q) (meaning997 q) hs
  change valuationOf q 995 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 995 = false ∨ valuation q 997 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 996 = true := by
  have hs : count996 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_left (literal (valuationOf q) (992)) (literal (valuationOf q) (996)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count996 q) 1 (meaning992 q) (meaning996 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 996 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 996 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 994 = false ∨ valuationOf q 997 = true := by
  have hs : count996 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (994)) (literal (valuationOf q) (997)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count996 q) 1 1 (meaning992 q) (meaning994 q) (meaning997 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 994 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 994 = false ∨ valuation q 997 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 995 = false ∨ valuationOf q 998 = true := by
  have hs : count996 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (995)) (literal (valuationOf q) (998)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count996 q) 1 2 (meaning992 q) (meaning995 q) (meaning998 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 995 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 995 = false ∨ valuation q 998 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 997 = true := by
  have hs : count996 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_left (literal (valuationOf q) (993)) (literal (valuationOf q) (997)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count996 q) 2 (meaning993 q) (meaning997 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 997 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 994 = false ∨ valuationOf q 998 = true := by
  have hs : count996 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (994)) (literal (valuationOf q) (998)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count996 q) 2 1 (meaning993 q) (meaning994 q) (meaning998 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 994 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 994 = false ∨ valuation q 998 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 995 = false ∨ valuationOf q 999 = true := by
  have hs : count996 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (995)) (literal (valuationOf q) (999)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count996 q) 2 2 (meaning993 q) (meaning995 q) (meaning999 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 995 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 995 = false ∨ valuation q 999 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1000 = true := by
  have hs : count1000 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1000)) (countLit q [-86]) (countLit q [-87]) (count1000 q) 1 (meaningNeg87 q) (meaning1000 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1000 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1000 = true := by
  have hs : count1000 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1000)) (countLit q [-86]) (countLit q [-87]) (count1000 q) 1 (meaningNeg86 q) (meaning1000 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1000 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 87 = true ∨ valuationOf q 1001 = true := by
  have hs : count1000 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (1001)) (countLit q [-86]) (countLit q [-87]) (count1000 q) 1 1 (meaningNeg86 q) (meaningNeg87 q) (meaning1001 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 87 = true ∨ valuation q 1001 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E097.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112097
