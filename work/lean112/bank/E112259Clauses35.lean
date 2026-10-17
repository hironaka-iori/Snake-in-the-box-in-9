import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 74 = true ∨ valuationOf q 926 = true := by
  have hs : count925 q = (countLit q [-69]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (926)) (countLit q [-69]) (countLit q [-74]) (count925 q) 1 1 (meaningNeg69 q) (meaningNeg74 q) (meaning926 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 74 = true ∨ valuation q 926 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 927 = true := by
  have hs : count927 q = (countLit q [-66, -68]) + (countLit q [-69, -74]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -74])
  have hm := merge_right (literal (valuationOf q) (925)) (literal (valuationOf q) (927)) (countLit q [-66, -68]) (countLit q [-69, -74]) (count927 q) 1 (meaning925 q) (meaning927 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 927 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 928 = true := by
  have hs : count927 q = (countLit q [-66, -68]) + (countLit q [-69, -74]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -74])
  have hm := merge_right (literal (valuationOf q) (926)) (literal (valuationOf q) (928)) (countLit q [-66, -68]) (countLit q [-69, -74]) (count927 q) 2 (meaning926 q) (meaning928 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 928 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 927 = true := by
  have hs : count927 q = (countLit q [-66, -68]) + (countLit q [-69, -74]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -74])
  have hm := merge_left (literal (valuationOf q) (923)) (literal (valuationOf q) (927)) (countLit q [-66, -68]) (countLit q [-69, -74]) (count927 q) 1 (meaning923 q) (meaning927 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 927 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 925 = false ∨ valuationOf q 928 = true := by
  have hs : count927 q = (countLit q [-66, -68]) + (countLit q [-69, -74]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -74])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (925)) (literal (valuationOf q) (928)) (countLit q [-66, -68]) (countLit q [-69, -74]) (count927 q) 1 1 (meaning923 q) (meaning925 q) (meaning928 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 925 = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 925 = false ∨ valuation q 928 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 926 = false ∨ valuationOf q 929 = true := by
  have hs : count927 q = (countLit q [-66, -68]) + (countLit q [-69, -74]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -74])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (926)) (literal (valuationOf q) (929)) (countLit q [-66, -68]) (countLit q [-69, -74]) (count927 q) 1 2 (meaning923 q) (meaning926 q) (meaning929 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 926 = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 926 = false ∨ valuation q 929 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 928 = true := by
  have hs : count927 q = (countLit q [-66, -68]) + (countLit q [-69, -74]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -74])
  have hm := merge_left (literal (valuationOf q) (924)) (literal (valuationOf q) (928)) (countLit q [-66, -68]) (countLit q [-69, -74]) (count927 q) 2 (meaning924 q) (meaning928 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 928 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 925 = false ∨ valuationOf q 929 = true := by
  have hs : count927 q = (countLit q [-66, -68]) + (countLit q [-69, -74]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -74])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (925)) (literal (valuationOf q) (929)) (countLit q [-66, -68]) (countLit q [-69, -74]) (count927 q) 2 1 (meaning924 q) (meaning925 q) (meaning929 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 925 = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 925 = false ∨ valuation q 929 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 926 = false ∨ valuationOf q 930 = true := by
  have hs : count927 q = (countLit q [-66, -68]) + (countLit q [-69, -74]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -74])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (926)) (literal (valuationOf q) (930)) (countLit q [-66, -68]) (countLit q [-69, -74]) (count927 q) 2 2 (meaning924 q) (meaning926 q) (meaning930 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 926 = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 926 = false ∨ valuation q 930 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 927 = false ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_right (literal (valuationOf q) (927)) (literal (valuationOf q) (931)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 1 (meaning927 q) (meaning931 q) hs
  change valuationOf q 927 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 927 = false ∨ valuation q 931 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 932 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_right (literal (valuationOf q) (928)) (literal (valuationOf q) (932)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 2 (meaning928 q) (meaning932 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 932 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 929 = false ∨ valuationOf q 933 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_right (literal (valuationOf q) (929)) (literal (valuationOf q) (933)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 3 (meaning929 q) (meaning933 q) hs
  change valuationOf q 929 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 929 = false ∨ valuation q 933 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_left (literal (valuationOf q) (920)) (literal (valuationOf q) (931)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 1 (meaning920 q) (meaning931 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 931 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 927 = false ∨ valuationOf q 932 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (927)) (literal (valuationOf q) (932)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 1 1 (meaning920 q) (meaning927 q) (meaning932 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 927 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 927 = false ∨ valuation q 932 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 928 = false ∨ valuationOf q 933 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (928)) (literal (valuationOf q) (933)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 1 2 (meaning920 q) (meaning928 q) (meaning933 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 928 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 928 = false ∨ valuation q 933 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 929 = false ∨ valuationOf q 934 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (929)) (literal (valuationOf q) (934)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 1 3 (meaning920 q) (meaning929 q) (meaning934 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 929 = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 929 = false ∨ valuation q 934 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 930 = false ∨ valuationOf q 935 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (930)) (literal (valuationOf q) (935)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 1 4 (meaning920 q) (meaning930 q) (meaning935 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 930 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 930 = false ∨ valuation q 935 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 932 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_left (literal (valuationOf q) (921)) (literal (valuationOf q) (932)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 2 (meaning921 q) (meaning932 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 932 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 927 = false ∨ valuationOf q 933 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (927)) (literal (valuationOf q) (933)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 2 1 (meaning921 q) (meaning927 q) (meaning933 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 927 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 927 = false ∨ valuation q 933 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 928 = false ∨ valuationOf q 934 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (928)) (literal (valuationOf q) (934)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 2 2 (meaning921 q) (meaning928 q) (meaning934 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 928 = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 928 = false ∨ valuation q 934 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 929 = false ∨ valuationOf q 935 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (929)) (literal (valuationOf q) (935)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 2 3 (meaning921 q) (meaning929 q) (meaning935 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 929 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 929 = false ∨ valuation q 935 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 933 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_left (literal (valuationOf q) (922)) (literal (valuationOf q) (933)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 3 (meaning922 q) (meaning933 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 933 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 927 = false ∨ valuationOf q 934 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (927)) (literal (valuationOf q) (934)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 3 1 (meaning922 q) (meaning927 q) (meaning934 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 927 = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 927 = false ∨ valuation q 934 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 928 = false ∨ valuationOf q 935 = true := by
  have hs : count931 q = (countLit q [-62, -63, -64]) + (countLit q [-66, -68, -69, -74]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-66, -68, -69, -74])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (928)) (literal (valuationOf q) (935)) (countLit q [-62, -63, -64]) (countLit q [-66, -68, -69, -74]) (count931 q) 3 2 (meaning922 q) (meaning928 q) (meaning935 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 928 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 928 = false ∨ valuation q 935 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-78]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (938)) (countLit q [-78]) (countLit q [-82]) (count938 q) 1 (meaningNeg82 q) (meaning938 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 938 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-78]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (938)) (countLit q [-78]) (countLit q [-82]) (count938 q) 1 (meaningNeg78 q) (meaning938 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 938 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 82 = true ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-78]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (939)) (countLit q [-78]) (countLit q [-82]) (count938 q) 1 1 (meaningNeg78 q) (meaningNeg82 q) (meaning939 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 82 = true ∨ valuation q 939 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 940 = true := by
  have hs : count940 q = (countLit q [-75]) + (countLit q [-78, -82]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-78, -82])
  have hm := merge_right (literal (valuationOf q) (938)) (literal (valuationOf q) (940)) (countLit q [-75]) (countLit q [-78, -82]) (count940 q) 1 (meaning938 q) (meaning940 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 940 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 939 = false ∨ valuationOf q 941 = true := by
  have hs : count940 q = (countLit q [-75]) + (countLit q [-78, -82]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-78, -82])
  have hm := merge_right (literal (valuationOf q) (939)) (literal (valuationOf q) (941)) (countLit q [-75]) (countLit q [-78, -82]) (count940 q) 2 (meaning939 q) (meaning941 q) hs
  change valuationOf q 939 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 939 = false ∨ valuation q 941 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 940 = true := by
  have hs : count940 q = (countLit q [-75]) + (countLit q [-78, -82]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-78, -82])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (940)) (countLit q [-75]) (countLit q [-78, -82]) (count940 q) 1 (meaningNeg75 q) (meaning940 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 940 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 938 = false ∨ valuationOf q 941 = true := by
  have hs : count940 q = (countLit q [-75]) + (countLit q [-78, -82]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-78, -82])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (938)) (literal (valuationOf q) (941)) (countLit q [-75]) (countLit q [-78, -82]) (count940 q) 1 1 (meaningNeg75 q) (meaning938 q) (meaning941 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 938 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 938 = false ∨ valuation q 941 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 939 = false ∨ valuationOf q 942 = true := by
  have hs : count940 q = (countLit q [-75]) + (countLit q [-78, -82]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-78, -82])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (939)) (literal (valuationOf q) (942)) (countLit q [-75]) (countLit q [-78, -82]) (count940 q) 1 2 (meaningNeg75 q) (meaning939 q) (meaning942 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 939 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 939 = false ∨ valuation q 942 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E259.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112259
