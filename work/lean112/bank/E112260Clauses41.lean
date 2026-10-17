import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 923 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_left (literal (valuationOf q) (912)) (literal (valuationOf q) (923)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 3 (meaning912 q) (meaning923 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 923 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 917 = false ∨ valuationOf q 924 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (917)) (literal (valuationOf q) (924)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 3 1 (meaning912 q) (meaning917 q) (meaning924 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 917 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 917 = false ∨ valuation q 924 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 918 = false ∨ valuationOf q 925 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (918)) (literal (valuationOf q) (925)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 3 2 (meaning912 q) (meaning918 q) (meaning925 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 918 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 918 = false ∨ valuation q 925 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 919 = false ∨ valuationOf q 926 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (919)) (literal (valuationOf q) (926)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 3 3 (meaning912 q) (meaning919 q) (meaning926 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 919 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 919 = false ∨ valuation q 926 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 928 = true := by
  have hs : count928 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (928)) (countLit q [-48]) (countLit q [-49]) (count928 q) 1 (meaningNeg49 q) (meaning928 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 928 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 928 = true := by
  have hs : count928 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (928)) (countLit q [-48]) (countLit q [-49]) (count928 q) 1 (meaningNeg48 q) (meaning928 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 928 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 49 = true ∨ valuationOf q 929 = true := by
  have hs : count928 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (929)) (countLit q [-48]) (countLit q [-49]) (count928 q) 1 1 (meaningNeg48 q) (meaningNeg49 q) (meaning929 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 929 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 930 = true := by
  have hs : count930 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (930)) (countLit q [-50]) (countLit q [-51]) (count930 q) 1 (meaningNeg51 q) (meaning930 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 930 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 930 = true := by
  have hs : count930 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (930)) (countLit q [-50]) (countLit q [-51]) (count930 q) 1 (meaningNeg50 q) (meaning930 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 930 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 51 = true ∨ valuationOf q 931 = true := by
  have hs : count930 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (931)) (countLit q [-50]) (countLit q [-51]) (count930 q) 1 1 (meaningNeg50 q) (meaningNeg51 q) (meaning931 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 931 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 930 = false ∨ valuationOf q 932 = true := by
  have hs : count932 q = (countLit q [-48, -49]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-50, -51])
  have hm := merge_right (literal (valuationOf q) (930)) (literal (valuationOf q) (932)) (countLit q [-48, -49]) (countLit q [-50, -51]) (count932 q) 1 (meaning930 q) (meaning932 q) hs
  change valuationOf q 930 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 930 = false ∨ valuation q 932 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 933 = true := by
  have hs : count932 q = (countLit q [-48, -49]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-50, -51])
  have hm := merge_right (literal (valuationOf q) (931)) (literal (valuationOf q) (933)) (countLit q [-48, -49]) (countLit q [-50, -51]) (count932 q) 2 (meaning931 q) (meaning933 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 933 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 932 = true := by
  have hs : count932 q = (countLit q [-48, -49]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-50, -51])
  have hm := merge_left (literal (valuationOf q) (928)) (literal (valuationOf q) (932)) (countLit q [-48, -49]) (countLit q [-50, -51]) (count932 q) 1 (meaning928 q) (meaning932 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 932 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 930 = false ∨ valuationOf q 933 = true := by
  have hs : count932 q = (countLit q [-48, -49]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (928)) (literal (valuationOf q) (930)) (literal (valuationOf q) (933)) (countLit q [-48, -49]) (countLit q [-50, -51]) (count932 q) 1 1 (meaning928 q) (meaning930 q) (meaning933 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 930 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 930 = false ∨ valuation q 933 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 931 = false ∨ valuationOf q 934 = true := by
  have hs : count932 q = (countLit q [-48, -49]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (928)) (literal (valuationOf q) (931)) (literal (valuationOf q) (934)) (countLit q [-48, -49]) (countLit q [-50, -51]) (count932 q) 1 2 (meaning928 q) (meaning931 q) (meaning934 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 931 = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 931 = false ∨ valuation q 934 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 929 = false ∨ valuationOf q 933 = true := by
  have hs : count932 q = (countLit q [-48, -49]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-50, -51])
  have hm := merge_left (literal (valuationOf q) (929)) (literal (valuationOf q) (933)) (countLit q [-48, -49]) (countLit q [-50, -51]) (count932 q) 2 (meaning929 q) (meaning933 q) hs
  change valuationOf q 929 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 929 = false ∨ valuation q 933 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 929 = false ∨ valuationOf q 930 = false ∨ valuationOf q 934 = true := by
  have hs : count932 q = (countLit q [-48, -49]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (929)) (literal (valuationOf q) (930)) (literal (valuationOf q) (934)) (countLit q [-48, -49]) (countLit q [-50, -51]) (count932 q) 2 1 (meaning929 q) (meaning930 q) (meaning934 q) hs
  change valuationOf q 929 = false ∨ valuationOf q 930 = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 929 = false ∨ valuation q 930 = false ∨ valuation q 934 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 929 = false ∨ valuationOf q 931 = false ∨ valuationOf q 935 = true := by
  have hs : count932 q = (countLit q [-48, -49]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (929)) (literal (valuationOf q) (931)) (literal (valuationOf q) (935)) (countLit q [-48, -49]) (countLit q [-50, -51]) (count932 q) 2 2 (meaning929 q) (meaning931 q) (meaning935 q) hs
  change valuationOf q 929 = false ∨ valuationOf q 931 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 929 = false ∨ valuation q 931 = false ∨ valuation q 935 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 936 = true := by
  have hs : count936 q = (countLit q [-56]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (936)) (countLit q [-56]) (countLit q [-60]) (count936 q) 1 (meaningNeg60 q) (meaning936 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 936 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 936 = true := by
  have hs : count936 q = (countLit q [-56]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (936)) (countLit q [-56]) (countLit q [-60]) (count936 q) 1 (meaningNeg56 q) (meaning936 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 936 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 60 = true ∨ valuationOf q 937 = true := by
  have hs : count936 q = (countLit q [-56]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-60])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-60)) (literal (valuationOf q) (937)) (countLit q [-56]) (countLit q [-60]) (count936 q) 1 1 (meaningNeg56 q) (meaningNeg60 q) (meaning937 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 60)) = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 60 = true ∨ valuation q 937 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (938)) (countLit q [-62]) (countLit q [-64]) (count938 q) 1 (meaningNeg64 q) (meaning938 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 938 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (938)) (countLit q [-62]) (countLit q [-64]) (count938 q) 1 (meaningNeg62 q) (meaning938 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 938 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 64 = true ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (-64)) (literal (valuationOf q) (939)) (countLit q [-62]) (countLit q [-64]) (count938 q) 1 1 (meaningNeg62 q) (meaningNeg64 q) (meaning939 q) hs
  change (! (valuationOf q 62)) = false ∨ (! (valuationOf q 64)) = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 64 = true ∨ valuation q 939 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 940 = true := by
  have hs : count940 q = (countLit q [-56, -60]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -64])
  have hm := merge_right (literal (valuationOf q) (938)) (literal (valuationOf q) (940)) (countLit q [-56, -60]) (countLit q [-62, -64]) (count940 q) 1 (meaning938 q) (meaning940 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 940 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 939 = false ∨ valuationOf q 941 = true := by
  have hs : count940 q = (countLit q [-56, -60]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -64])
  have hm := merge_right (literal (valuationOf q) (939)) (literal (valuationOf q) (941)) (countLit q [-56, -60]) (countLit q [-62, -64]) (count940 q) 2 (meaning939 q) (meaning941 q) hs
  change valuationOf q 939 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 939 = false ∨ valuation q 941 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 940 = true := by
  have hs : count940 q = (countLit q [-56, -60]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -64])
  have hm := merge_left (literal (valuationOf q) (936)) (literal (valuationOf q) (940)) (countLit q [-56, -60]) (countLit q [-62, -64]) (count940 q) 1 (meaning936 q) (meaning940 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 940 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 938 = false ∨ valuationOf q 941 = true := by
  have hs : count940 q = (countLit q [-56, -60]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -64])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (938)) (literal (valuationOf q) (941)) (countLit q [-56, -60]) (countLit q [-62, -64]) (count940 q) 1 1 (meaning936 q) (meaning938 q) (meaning941 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 938 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 938 = false ∨ valuation q 941 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 939 = false ∨ valuationOf q 942 = true := by
  have hs : count940 q = (countLit q [-56, -60]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -64])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (939)) (literal (valuationOf q) (942)) (countLit q [-56, -60]) (countLit q [-62, -64]) (count940 q) 1 2 (meaning936 q) (meaning939 q) (meaning942 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 939 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 939 = false ∨ valuation q 942 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 941 = true := by
  have hs : count940 q = (countLit q [-56, -60]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -64])
  have hm := merge_left (literal (valuationOf q) (937)) (literal (valuationOf q) (941)) (countLit q [-56, -60]) (countLit q [-62, -64]) (count940 q) 2 (meaning937 q) (meaning941 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 941 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 938 = false ∨ valuationOf q 942 = true := by
  have hs : count940 q = (countLit q [-56, -60]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -64])
  have hm := merge_two (literal (valuationOf q) (937)) (literal (valuationOf q) (938)) (literal (valuationOf q) (942)) (countLit q [-56, -60]) (countLit q [-62, -64]) (count940 q) 2 1 (meaning937 q) (meaning938 q) (meaning942 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 938 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 938 = false ∨ valuation q 942 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 939 = false ∨ valuationOf q 943 = true := by
  have hs : count940 q = (countLit q [-56, -60]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -64])
  have hm := merge_two (literal (valuationOf q) (937)) (literal (valuationOf q) (939)) (literal (valuationOf q) (943)) (countLit q [-56, -60]) (countLit q [-62, -64]) (count940 q) 2 2 (meaning937 q) (meaning939 q) (meaning943 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 939 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 939 = false ∨ valuation q 943 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E260.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112260
