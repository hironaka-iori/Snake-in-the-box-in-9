import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 945 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_left (literal (valuationOf q) (933)) (literal (valuationOf q) (945)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 2 (meaning933 q) (meaning945 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 945 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 940 = false ∨ valuationOf q 946 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (940)) (literal (valuationOf q) (946)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 2 1 (meaning933 q) (meaning940 q) (meaning946 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 940 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 940 = false ∨ valuation q 946 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 941 = false ∨ valuationOf q 947 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (941)) (literal (valuationOf q) (947)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 2 2 (meaning933 q) (meaning941 q) (meaning947 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 941 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 941 = false ∨ valuation q 947 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 942 = false ∨ valuationOf q 948 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (942)) (literal (valuationOf q) (948)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 2 3 (meaning933 q) (meaning942 q) (meaning948 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 942 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 942 = false ∨ valuation q 948 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 943 = false ∨ valuationOf q 949 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (943)) (literal (valuationOf q) (949)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 2 4 (meaning933 q) (meaning943 q) (meaning949 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 943 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 943 = false ∨ valuation q 949 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 946 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_left (literal (valuationOf q) (934)) (literal (valuationOf q) (946)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 3 (meaning934 q) (meaning946 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 946 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 940 = false ∨ valuationOf q 947 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (940)) (literal (valuationOf q) (947)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 3 1 (meaning934 q) (meaning940 q) (meaning947 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 940 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 940 = false ∨ valuation q 947 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 941 = false ∨ valuationOf q 948 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (941)) (literal (valuationOf q) (948)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 3 2 (meaning934 q) (meaning941 q) (meaning948 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 941 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 941 = false ∨ valuation q 948 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 942 = false ∨ valuationOf q 949 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (942)) (literal (valuationOf q) (949)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 3 3 (meaning934 q) (meaning942 q) (meaning949 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 942 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 942 = false ∨ valuation q 949 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 940 = false ∨ valuationOf q 948 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (940)) (literal (valuationOf q) (948)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 4 1 (meaning935 q) (meaning940 q) (meaning948 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 940 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 940 = false ∨ valuation q 948 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 941 = false ∨ valuationOf q 949 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (941)) (literal (valuationOf q) (949)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 4 2 (meaning935 q) (meaning941 q) (meaning949 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 941 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 941 = false ∨ valuation q 949 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 952 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_right (literal (valuationOf q) (944)) (literal (valuationOf q) (952)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 1 (meaning944 q) (meaning952 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 952 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 953 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_right (literal (valuationOf q) (945)) (literal (valuationOf q) (953)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 2 (meaning945 q) (meaning953 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 953 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 954 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_right (literal (valuationOf q) (946)) (literal (valuationOf q) (954)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 3 (meaning946 q) (meaning954 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 954 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 955 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_right (literal (valuationOf q) (947)) (literal (valuationOf q) (955)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 4 (meaning947 q) (meaning955 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 955 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 956 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_right (literal (valuationOf q) (948)) (literal (valuationOf q) (956)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 5 (meaning948 q) (meaning956 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 956 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_right (literal (valuationOf q) (949)) (literal (valuationOf q) (957)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 6 (meaning949 q) (meaning957 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 957 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 952 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_left (literal (valuationOf q) (921)) (literal (valuationOf q) (952)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 1 (meaning921 q) (meaning952 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 952 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 944 = false ∨ valuationOf q 953 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (944)) (literal (valuationOf q) (953)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 1 1 (meaning921 q) (meaning944 q) (meaning953 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 944 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 944 = false ∨ valuation q 953 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 945 = false ∨ valuationOf q 954 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (945)) (literal (valuationOf q) (954)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 1 2 (meaning921 q) (meaning945 q) (meaning954 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 945 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 945 = false ∨ valuation q 954 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 946 = false ∨ valuationOf q 955 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (946)) (literal (valuationOf q) (955)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 1 3 (meaning921 q) (meaning946 q) (meaning955 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 946 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 946 = false ∨ valuation q 955 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 947 = false ∨ valuationOf q 956 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (947)) (literal (valuationOf q) (956)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 1 4 (meaning921 q) (meaning947 q) (meaning956 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 947 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 947 = false ∨ valuation q 956 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 948 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (948)) (literal (valuationOf q) (957)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 1 5 (meaning921 q) (meaning948 q) (meaning957 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 948 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 948 = false ∨ valuation q 957 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 949 = false ∨ valuationOf q 958 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (949)) (literal (valuationOf q) (958)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 1 6 (meaning921 q) (meaning949 q) (meaning958 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 949 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 949 = false ∨ valuation q 958 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 953 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_left (literal (valuationOf q) (922)) (literal (valuationOf q) (953)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 2 (meaning922 q) (meaning953 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 953 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 944 = false ∨ valuationOf q 954 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (944)) (literal (valuationOf q) (954)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 2 1 (meaning922 q) (meaning944 q) (meaning954 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 944 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 944 = false ∨ valuation q 954 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 945 = false ∨ valuationOf q 955 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (945)) (literal (valuationOf q) (955)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 2 2 (meaning922 q) (meaning945 q) (meaning955 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 945 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 945 = false ∨ valuation q 955 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 946 = false ∨ valuationOf q 956 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (946)) (literal (valuationOf q) (956)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 2 3 (meaning922 q) (meaning946 q) (meaning956 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 946 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 946 = false ∨ valuation q 956 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 947 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (947)) (literal (valuationOf q) (957)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 2 4 (meaning922 q) (meaning947 q) (meaning957 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 947 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 947 = false ∨ valuation q 957 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 948 = false ∨ valuationOf q 958 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (948)) (literal (valuationOf q) (958)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 2 5 (meaning922 q) (meaning948 q) (meaning958 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 948 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 948 = false ∨ valuation q 958 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 949 = false ∨ valuationOf q 959 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (949)) (literal (valuationOf q) (959)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 2 6 (meaning922 q) (meaning949 q) (meaning959 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 949 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 949 = false ∨ valuation q 959 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 954 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_left (literal (valuationOf q) (923)) (literal (valuationOf q) (954)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 3 (meaning923 q) (meaning954 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 954 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E256.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112256
