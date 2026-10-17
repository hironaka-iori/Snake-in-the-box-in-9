import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 53 = true ∨ valuationOf q 931 = true := by
  have hs : count930 q = (countLit q [-49]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (931)) (countLit q [-49]) (countLit q [-53]) (count930 q) 1 1 (meaningNeg49 q) (meaningNeg53 q) (meaning931 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 53 = true ∨ valuation q 931 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 930 = false ∨ valuationOf q 932 = true := by
  have hs : count932 q = (countLit q [-45, -47]) + (countLit q [-49, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -53])
  have hm := merge_right (literal (valuationOf q) (930)) (literal (valuationOf q) (932)) (countLit q [-45, -47]) (countLit q [-49, -53]) (count932 q) 1 (meaning930 q) (meaning932 q) hs
  change valuationOf q 930 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 930 = false ∨ valuation q 932 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 933 = true := by
  have hs : count932 q = (countLit q [-45, -47]) + (countLit q [-49, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -53])
  have hm := merge_right (literal (valuationOf q) (931)) (literal (valuationOf q) (933)) (countLit q [-45, -47]) (countLit q [-49, -53]) (count932 q) 2 (meaning931 q) (meaning933 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 933 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 932 = true := by
  have hs : count932 q = (countLit q [-45, -47]) + (countLit q [-49, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -53])
  have hm := merge_left (literal (valuationOf q) (928)) (literal (valuationOf q) (932)) (countLit q [-45, -47]) (countLit q [-49, -53]) (count932 q) 1 (meaning928 q) (meaning932 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 932 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 930 = false ∨ valuationOf q 933 = true := by
  have hs : count932 q = (countLit q [-45, -47]) + (countLit q [-49, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -53])
  have hm := merge_two (literal (valuationOf q) (928)) (literal (valuationOf q) (930)) (literal (valuationOf q) (933)) (countLit q [-45, -47]) (countLit q [-49, -53]) (count932 q) 1 1 (meaning928 q) (meaning930 q) (meaning933 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 930 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 930 = false ∨ valuation q 933 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 931 = false ∨ valuationOf q 934 = true := by
  have hs : count932 q = (countLit q [-45, -47]) + (countLit q [-49, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -53])
  have hm := merge_two (literal (valuationOf q) (928)) (literal (valuationOf q) (931)) (literal (valuationOf q) (934)) (countLit q [-45, -47]) (countLit q [-49, -53]) (count932 q) 1 2 (meaning928 q) (meaning931 q) (meaning934 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 931 = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 931 = false ∨ valuation q 934 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 929 = false ∨ valuationOf q 933 = true := by
  have hs : count932 q = (countLit q [-45, -47]) + (countLit q [-49, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -53])
  have hm := merge_left (literal (valuationOf q) (929)) (literal (valuationOf q) (933)) (countLit q [-45, -47]) (countLit q [-49, -53]) (count932 q) 2 (meaning929 q) (meaning933 q) hs
  change valuationOf q 929 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 929 = false ∨ valuation q 933 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 929 = false ∨ valuationOf q 930 = false ∨ valuationOf q 934 = true := by
  have hs : count932 q = (countLit q [-45, -47]) + (countLit q [-49, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -53])
  have hm := merge_two (literal (valuationOf q) (929)) (literal (valuationOf q) (930)) (literal (valuationOf q) (934)) (countLit q [-45, -47]) (countLit q [-49, -53]) (count932 q) 2 1 (meaning929 q) (meaning930 q) (meaning934 q) hs
  change valuationOf q 929 = false ∨ valuationOf q 930 = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 929 = false ∨ valuation q 930 = false ∨ valuation q 934 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 929 = false ∨ valuationOf q 931 = false ∨ valuationOf q 935 = true := by
  have hs : count932 q = (countLit q [-45, -47]) + (countLit q [-49, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -53])
  have hm := merge_two (literal (valuationOf q) (929)) (literal (valuationOf q) (931)) (literal (valuationOf q) (935)) (countLit q [-45, -47]) (countLit q [-49, -53]) (count932 q) 2 2 (meaning929 q) (meaning931 q) (meaning935 q) hs
  change valuationOf q 929 = false ∨ valuationOf q 931 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 929 = false ∨ valuation q 931 = false ∨ valuation q 935 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 936 = true := by
  have hs : count936 q = (countLit q [-57]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (936)) (countLit q [-57]) (countLit q [-58]) (count936 q) 1 (meaningNeg58 q) (meaning936 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 936 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 936 = true := by
  have hs : count936 q = (countLit q [-57]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (936)) (countLit q [-57]) (countLit q [-58]) (count936 q) 1 (meaningNeg57 q) (meaning936 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 936 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 58 = true ∨ valuationOf q 937 = true := by
  have hs : count936 q = (countLit q [-57]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (-58)) (literal (valuationOf q) (937)) (countLit q [-57]) (countLit q [-58]) (count936 q) 1 1 (meaningNeg57 q) (meaningNeg58 q) (meaning937 q) hs
  change (! (valuationOf q 57)) = false ∨ (! (valuationOf q 58)) = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 58 = true ∨ valuation q 937 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-60]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61])
  have hm := merge_right (literal (valuationOf q) (-61)) (literal (valuationOf q) (938)) (countLit q [-60]) (countLit q [-61]) (count938 q) 1 (meaningNeg61 q) (meaning938 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 938 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-60]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (938)) (countLit q [-60]) (countLit q [-61]) (count938 q) 1 (meaningNeg60 q) (meaning938 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 938 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 61 = true ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-60]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (-61)) (literal (valuationOf q) (939)) (countLit q [-60]) (countLit q [-61]) (count938 q) 1 1 (meaningNeg60 q) (meaningNeg61 q) (meaning939 q) hs
  change (! (valuationOf q 60)) = false ∨ (! (valuationOf q 61)) = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 61 = true ∨ valuation q 939 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 940 = true := by
  have hs : count940 q = (countLit q [-57, -58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-57, -58]) (l₂ := [-60, -61])
  have hm := merge_right (literal (valuationOf q) (938)) (literal (valuationOf q) (940)) (countLit q [-57, -58]) (countLit q [-60, -61]) (count940 q) 1 (meaning938 q) (meaning940 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 940 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 939 = false ∨ valuationOf q 941 = true := by
  have hs : count940 q = (countLit q [-57, -58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-57, -58]) (l₂ := [-60, -61])
  have hm := merge_right (literal (valuationOf q) (939)) (literal (valuationOf q) (941)) (countLit q [-57, -58]) (countLit q [-60, -61]) (count940 q) 2 (meaning939 q) (meaning941 q) hs
  change valuationOf q 939 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 939 = false ∨ valuation q 941 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 940 = true := by
  have hs : count940 q = (countLit q [-57, -58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-57, -58]) (l₂ := [-60, -61])
  have hm := merge_left (literal (valuationOf q) (936)) (literal (valuationOf q) (940)) (countLit q [-57, -58]) (countLit q [-60, -61]) (count940 q) 1 (meaning936 q) (meaning940 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 940 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 938 = false ∨ valuationOf q 941 = true := by
  have hs : count940 q = (countLit q [-57, -58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-57, -58]) (l₂ := [-60, -61])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (938)) (literal (valuationOf q) (941)) (countLit q [-57, -58]) (countLit q [-60, -61]) (count940 q) 1 1 (meaning936 q) (meaning938 q) (meaning941 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 938 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 938 = false ∨ valuation q 941 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 939 = false ∨ valuationOf q 942 = true := by
  have hs : count940 q = (countLit q [-57, -58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-57, -58]) (l₂ := [-60, -61])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (939)) (literal (valuationOf q) (942)) (countLit q [-57, -58]) (countLit q [-60, -61]) (count940 q) 1 2 (meaning936 q) (meaning939 q) (meaning942 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 939 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 939 = false ∨ valuation q 942 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 941 = true := by
  have hs : count940 q = (countLit q [-57, -58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-57, -58]) (l₂ := [-60, -61])
  have hm := merge_left (literal (valuationOf q) (937)) (literal (valuationOf q) (941)) (countLit q [-57, -58]) (countLit q [-60, -61]) (count940 q) 2 (meaning937 q) (meaning941 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 941 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 938 = false ∨ valuationOf q 942 = true := by
  have hs : count940 q = (countLit q [-57, -58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-57, -58]) (l₂ := [-60, -61])
  have hm := merge_two (literal (valuationOf q) (937)) (literal (valuationOf q) (938)) (literal (valuationOf q) (942)) (countLit q [-57, -58]) (countLit q [-60, -61]) (count940 q) 2 1 (meaning937 q) (meaning938 q) (meaning942 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 938 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 938 = false ∨ valuation q 942 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 939 = false ∨ valuationOf q 943 = true := by
  have hs : count940 q = (countLit q [-57, -58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-57, -58]) (l₂ := [-60, -61])
  have hm := merge_two (literal (valuationOf q) (937)) (literal (valuationOf q) (939)) (literal (valuationOf q) (943)) (countLit q [-57, -58]) (countLit q [-60, -61]) (count940 q) 2 2 (meaning937 q) (meaning939 q) (meaning943 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 939 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 939 = false ∨ valuation q 943 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 944 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_right (literal (valuationOf q) (940)) (literal (valuationOf q) (944)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 1 (meaning940 q) (meaning944 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 944 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 941 = false ∨ valuationOf q 945 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_right (literal (valuationOf q) (941)) (literal (valuationOf q) (945)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 2 (meaning941 q) (meaning945 q) hs
  change valuationOf q 941 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 941 = false ∨ valuation q 945 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 946 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_right (literal (valuationOf q) (942)) (literal (valuationOf q) (946)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 3 (meaning942 q) (meaning946 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 946 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 947 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_right (literal (valuationOf q) (943)) (literal (valuationOf q) (947)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 4 (meaning943 q) (meaning947 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 947 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 944 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_left (literal (valuationOf q) (932)) (literal (valuationOf q) (944)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 1 (meaning932 q) (meaning944 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 944 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 940 = false ∨ valuationOf q 945 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (940)) (literal (valuationOf q) (945)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 1 1 (meaning932 q) (meaning940 q) (meaning945 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 940 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 940 = false ∨ valuation q 945 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 941 = false ∨ valuationOf q 946 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (941)) (literal (valuationOf q) (946)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 1 2 (meaning932 q) (meaning941 q) (meaning946 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 941 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 941 = false ∨ valuation q 946 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 942 = false ∨ valuationOf q 947 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (942)) (literal (valuationOf q) (947)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 1 3 (meaning932 q) (meaning942 q) (meaning947 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 942 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 942 = false ∨ valuation q 947 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 943 = false ∨ valuationOf q 948 = true := by
  have hs : count944 q = (countLit q [-45, -47, -49, -53]) + (countLit q [-57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-45, -47, -49, -53]) (l₂ := [-57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (943)) (literal (valuationOf q) (948)) (countLit q [-45, -47, -49, -53]) (countLit q [-57, -58, -60, -61]) (count944 q) 1 4 (meaning932 q) (meaning943 q) (meaning948 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 943 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 943 = false ∨ valuation q 948 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E256.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112256
