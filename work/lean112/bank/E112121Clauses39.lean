import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 937 = true := by
  have hs : count937 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (937)) (countLit q [-43]) (countLit q [-44]) (count937 q) 1 (meaningNeg43 q) (meaning937 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 937 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 44 = true ∨ valuationOf q 938 = true := by
  have hs : count937 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (938)) (countLit q [-43]) (countLit q [-44]) (count937 q) 1 1 (meaningNeg43 q) (meaningNeg44 q) (meaning938 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 938 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 939 = true := by
  have hs : count939 q = (countLit q [-38, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -42]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (935)) (literal (valuationOf q) (939)) (countLit q [-38, -42]) (countLit q [-43, -44]) (count939 q) 1 (meaning935 q) (meaning939 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 939 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 937 = false ∨ valuationOf q 940 = true := by
  have hs : count939 q = (countLit q [-38, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -42]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (937)) (literal (valuationOf q) (940)) (countLit q [-38, -42]) (countLit q [-43, -44]) (count939 q) 1 1 (meaning935 q) (meaning937 q) (meaning940 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 937 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 937 = false ∨ valuation q 940 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 938 = false ∨ valuationOf q 941 = true := by
  have hs : count939 q = (countLit q [-38, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -42]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (938)) (literal (valuationOf q) (941)) (countLit q [-38, -42]) (countLit q [-43, -44]) (count939 q) 1 2 (meaning935 q) (meaning938 q) (meaning941 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 938 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 938 = false ∨ valuation q 941 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 940 = true := by
  have hs : count939 q = (countLit q [-38, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -42]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (936)) (literal (valuationOf q) (940)) (countLit q [-38, -42]) (countLit q [-43, -44]) (count939 q) 2 (meaning936 q) (meaning940 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 940 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 937 = false ∨ valuationOf q 941 = true := by
  have hs : count939 q = (countLit q [-38, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -42]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (937)) (literal (valuationOf q) (941)) (countLit q [-38, -42]) (countLit q [-43, -44]) (count939 q) 2 1 (meaning936 q) (meaning937 q) (meaning941 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 937 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 937 = false ∨ valuation q 941 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 938 = false ∨ valuationOf q 942 = true := by
  have hs : count939 q = (countLit q [-38, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -42]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (938)) (literal (valuationOf q) (942)) (countLit q [-38, -42]) (countLit q [-43, -44]) (count939 q) 2 2 (meaning936 q) (meaning938 q) (meaning942 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 938 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 938 = false ∨ valuation q 942 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 939 = false ∨ valuationOf q 943 = true := by
  have hs : count943 q = (countLit q [-32, -34, -35, -36]) + (countLit q [-38, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36]) (l₂ := [-38, -42, -43, -44])
  have hm := merge_right (literal (valuationOf q) (939)) (literal (valuationOf q) (943)) (countLit q [-32, -34, -35, -36]) (countLit q [-38, -42, -43, -44]) (count943 q) 1 (meaning939 q) (meaning943 q) hs
  change valuationOf q 939 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 939 = false ∨ valuation q 943 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 939 = false ∨ valuationOf q 944 = true := by
  have hs : count943 q = (countLit q [-32, -34, -35, -36]) + (countLit q [-38, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36]) (l₂ := [-38, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (939)) (literal (valuationOf q) (944)) (countLit q [-32, -34, -35, -36]) (countLit q [-38, -42, -43, -44]) (count943 q) 1 1 (meaning931 q) (meaning939 q) (meaning944 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 939 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 939 = false ∨ valuation q 944 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 939 = false ∨ valuationOf q 945 = true := by
  have hs : count943 q = (countLit q [-32, -34, -35, -36]) + (countLit q [-38, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36]) (l₂ := [-38, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (939)) (literal (valuationOf q) (945)) (countLit q [-32, -34, -35, -36]) (countLit q [-38, -42, -43, -44]) (count943 q) 2 1 (meaning932 q) (meaning939 q) (meaning945 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 939 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 939 = false ∨ valuation q 945 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 940 = false ∨ valuationOf q 946 = true := by
  have hs : count943 q = (countLit q [-32, -34, -35, -36]) + (countLit q [-38, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36]) (l₂ := [-38, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (940)) (literal (valuationOf q) (946)) (countLit q [-32, -34, -35, -36]) (countLit q [-38, -42, -43, -44]) (count943 q) 2 2 (meaning932 q) (meaning940 q) (meaning946 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 940 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 940 = false ∨ valuation q 946 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 941 = false ∨ valuationOf q 947 = true := by
  have hs : count943 q = (countLit q [-32, -34, -35, -36]) + (countLit q [-38, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36]) (l₂ := [-38, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (941)) (literal (valuationOf q) (947)) (countLit q [-32, -34, -35, -36]) (countLit q [-38, -42, -43, -44]) (count943 q) 2 3 (meaning932 q) (meaning941 q) (meaning947 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 941 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 941 = false ∨ valuation q 947 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 939 = false ∨ valuationOf q 946 = true := by
  have hs : count943 q = (countLit q [-32, -34, -35, -36]) + (countLit q [-38, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36]) (l₂ := [-38, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (939)) (literal (valuationOf q) (946)) (countLit q [-32, -34, -35, -36]) (countLit q [-38, -42, -43, -44]) (count943 q) 3 1 (meaning933 q) (meaning939 q) (meaning946 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 939 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 939 = false ∨ valuation q 946 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 940 = false ∨ valuationOf q 947 = true := by
  have hs : count943 q = (countLit q [-32, -34, -35, -36]) + (countLit q [-38, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36]) (l₂ := [-38, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (940)) (literal (valuationOf q) (947)) (countLit q [-32, -34, -35, -36]) (countLit q [-38, -42, -43, -44]) (count943 q) 3 2 (meaning933 q) (meaning940 q) (meaning947 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 940 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 940 = false ∨ valuation q 947 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 941 = false ∨ valuationOf q 948 = true := by
  have hs : count943 q = (countLit q [-32, -34, -35, -36]) + (countLit q [-38, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36]) (l₂ := [-38, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (941)) (literal (valuationOf q) (948)) (countLit q [-32, -34, -35, -36]) (countLit q [-38, -42, -43, -44]) (count943 q) 3 3 (meaning933 q) (meaning941 q) (meaning948 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 941 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 941 = false ∨ valuation q 948 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 942 = false ∨ valuationOf q 949 = true := by
  have hs : count943 q = (countLit q [-32, -34, -35, -36]) + (countLit q [-38, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36]) (l₂ := [-38, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (942)) (literal (valuationOf q) (949)) (countLit q [-32, -34, -35, -36]) (countLit q [-38, -42, -43, -44]) (count943 q) 3 4 (meaning933 q) (meaning942 q) (meaning949 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 942 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 942 = false ∨ valuation q 949 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 939 = false ∨ valuationOf q 947 = true := by
  have hs : count943 q = (countLit q [-32, -34, -35, -36]) + (countLit q [-38, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36]) (l₂ := [-38, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (939)) (literal (valuationOf q) (947)) (countLit q [-32, -34, -35, -36]) (countLit q [-38, -42, -43, -44]) (count943 q) 4 1 (meaning934 q) (meaning939 q) (meaning947 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 939 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 939 = false ∨ valuation q 947 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 940 = false ∨ valuationOf q 948 = true := by
  have hs : count943 q = (countLit q [-32, -34, -35, -36]) + (countLit q [-38, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36]) (l₂ := [-38, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (940)) (literal (valuationOf q) (948)) (countLit q [-32, -34, -35, -36]) (countLit q [-38, -42, -43, -44]) (count943 q) 4 2 (meaning934 q) (meaning940 q) (meaning948 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 940 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 940 = false ∨ valuation q 948 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 951 = true := by
  have hs : count951 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (951)) (countLit q [-46]) (countLit q [-47]) (count951 q) 1 (meaningNeg47 q) (meaning951 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 951 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 951 = true := by
  have hs : count951 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (951)) (countLit q [-46]) (countLit q [-47]) (count951 q) 1 (meaningNeg46 q) (meaning951 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 951 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 47 = true ∨ valuationOf q 952 = true := by
  have hs : count951 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (952)) (countLit q [-46]) (countLit q [-47]) (count951 q) 1 1 (meaningNeg46 q) (meaningNeg47 q) (meaning952 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 952 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-51]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (953)) (countLit q [-51]) (countLit q [-53]) (count953 q) 1 (meaningNeg53 q) (meaning953 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 953 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-51]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (953)) (countLit q [-51]) (countLit q [-53]) (count953 q) 1 (meaningNeg51 q) (meaning953 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 953 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 53 = true ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-51]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (954)) (countLit q [-51]) (countLit q [-53]) (count953 q) 1 1 (meaningNeg51 q) (meaningNeg53 q) (meaning954 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 954 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 955 = true := by
  have hs : count955 q = (countLit q [-46, -47]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-51, -53])
  have hm := merge_right (literal (valuationOf q) (953)) (literal (valuationOf q) (955)) (countLit q [-46, -47]) (countLit q [-51, -53]) (count955 q) 1 (meaning953 q) (meaning955 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 955 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 956 = true := by
  have hs : count955 q = (countLit q [-46, -47]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-51, -53])
  have hm := merge_right (literal (valuationOf q) (954)) (literal (valuationOf q) (956)) (countLit q [-46, -47]) (countLit q [-51, -53]) (count955 q) 2 (meaning954 q) (meaning956 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 956 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 955 = true := by
  have hs : count955 q = (countLit q [-46, -47]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-51, -53])
  have hm := merge_left (literal (valuationOf q) (951)) (literal (valuationOf q) (955)) (countLit q [-46, -47]) (countLit q [-51, -53]) (count955 q) 1 (meaning951 q) (meaning955 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 955 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 953 = false ∨ valuationOf q 956 = true := by
  have hs : count955 q = (countLit q [-46, -47]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-51, -53])
  have hm := merge_two (literal (valuationOf q) (951)) (literal (valuationOf q) (953)) (literal (valuationOf q) (956)) (countLit q [-46, -47]) (countLit q [-51, -53]) (count955 q) 1 1 (meaning951 q) (meaning953 q) (meaning956 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 953 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 953 = false ∨ valuation q 956 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 954 = false ∨ valuationOf q 957 = true := by
  have hs : count955 q = (countLit q [-46, -47]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-51, -53])
  have hm := merge_two (literal (valuationOf q) (951)) (literal (valuationOf q) (954)) (literal (valuationOf q) (957)) (countLit q [-46, -47]) (countLit q [-51, -53]) (count955 q) 1 2 (meaning951 q) (meaning954 q) (meaning957 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 954 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 954 = false ∨ valuation q 957 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 956 = true := by
  have hs : count955 q = (countLit q [-46, -47]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-51, -53])
  have hm := merge_left (literal (valuationOf q) (952)) (literal (valuationOf q) (956)) (countLit q [-46, -47]) (countLit q [-51, -53]) (count955 q) 2 (meaning952 q) (meaning956 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 956 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 953 = false ∨ valuationOf q 957 = true := by
  have hs : count955 q = (countLit q [-46, -47]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-51, -53])
  have hm := merge_two (literal (valuationOf q) (952)) (literal (valuationOf q) (953)) (literal (valuationOf q) (957)) (countLit q [-46, -47]) (countLit q [-51, -53]) (count955 q) 2 1 (meaning952 q) (meaning953 q) (meaning957 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 953 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 953 = false ∨ valuation q 957 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E121.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112121
