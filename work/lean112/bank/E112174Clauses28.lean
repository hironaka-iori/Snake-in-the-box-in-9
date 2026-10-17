import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1316 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1252)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1316)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 7 2 (meaning1252 q) (meaning1296 q) (meaning1316 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1296 = false ∨ valuation q 1316 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1317 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1252)) (literal (valuationOf q) (1297)) (literal (valuationOf q) (1317)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 7 3 (meaning1252 q) (meaning1297 q) (meaning1317 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1297 = false ∨ valuation q 1317 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1317 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1253)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1317)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 8 2 (meaning1253 q) (meaning1296 q) (meaning1317 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1296 = false ∨ valuation q 1317 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1321 = true := by
  have hs : count1321 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (1321)) (countLit q [-54]) (countLit q [-55]) (count1321 q) 1 (meaningNeg55 q) (meaning1321 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1321 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1321 = true := by
  have hs : count1321 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1321)) (countLit q [-54]) (countLit q [-55]) (count1321 q) 1 (meaningNeg54 q) (meaning1321 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1321 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 55 = true ∨ valuationOf q 1322 = true := by
  have hs : count1321 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (1322)) (countLit q [-54]) (countLit q [-55]) (count1321 q) 1 1 (meaningNeg54 q) (meaningNeg55 q) (meaning1322 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 1322 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1323 = true := by
  have hs : count1323 q = (countLit q [-52]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54, -55])
  have hm := merge_right (literal (valuationOf q) (1321)) (literal (valuationOf q) (1323)) (countLit q [-52]) (countLit q [-54, -55]) (count1323 q) 1 (meaning1321 q) (meaning1323 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1323 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1324 = true := by
  have hs : count1323 q = (countLit q [-52]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54, -55])
  have hm := merge_right (literal (valuationOf q) (1322)) (literal (valuationOf q) (1324)) (countLit q [-52]) (countLit q [-54, -55]) (count1323 q) 2 (meaning1322 q) (meaning1324 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1324 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1323 = true := by
  have hs : count1323 q = (countLit q [-52]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54, -55])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1323)) (countLit q [-52]) (countLit q [-54, -55]) (count1323 q) 1 (meaningNeg52 q) (meaning1323 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1323 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1321 = false ∨ valuationOf q 1324 = true := by
  have hs : count1323 q = (countLit q [-52]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54, -55])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1324)) (countLit q [-52]) (countLit q [-54, -55]) (count1323 q) 1 1 (meaningNeg52 q) (meaning1321 q) (meaning1324 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1321 = false ∨ valuation q 1324 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1322 = false ∨ valuationOf q 1325 = true := by
  have hs : count1323 q = (countLit q [-52]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54, -55])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1325)) (countLit q [-52]) (countLit q [-54, -55]) (count1323 q) 1 2 (meaningNeg52 q) (meaning1322 q) (meaning1325 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1322 = false ∨ valuation q 1325 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1326)) (countLit q [-60]) (countLit q [-62]) (count1326 q) 1 (meaningNeg62 q) (meaning1326 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1326 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1326)) (countLit q [-60]) (countLit q [-62]) (count1326 q) 1 (meaningNeg60 q) (meaning1326 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1326 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 62 = true ∨ valuationOf q 1327 = true := by
  have hs : count1326 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (1327)) (countLit q [-60]) (countLit q [-62]) (count1326 q) 1 1 (meaningNeg60 q) (meaningNeg62 q) (meaning1327 q) hs
  change (! (valuationOf q 60)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 62 = true ∨ valuation q 1327 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1328 = true := by
  have hs : count1328 q = (countLit q [-57]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60, -62])
  have hm := merge_right (literal (valuationOf q) (1326)) (literal (valuationOf q) (1328)) (countLit q [-57]) (countLit q [-60, -62]) (count1328 q) 1 (meaning1326 q) (meaning1328 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1328 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1329 = true := by
  have hs : count1328 q = (countLit q [-57]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60, -62])
  have hm := merge_right (literal (valuationOf q) (1327)) (literal (valuationOf q) (1329)) (countLit q [-57]) (countLit q [-60, -62]) (count1328 q) 2 (meaning1327 q) (meaning1329 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1329 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1328 = true := by
  have hs : count1328 q = (countLit q [-57]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60, -62])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (1328)) (countLit q [-57]) (countLit q [-60, -62]) (count1328 q) 1 (meaningNeg57 q) (meaning1328 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1328 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1326 = false ∨ valuationOf q 1329 = true := by
  have hs : count1328 q = (countLit q [-57]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60, -62])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (1326)) (literal (valuationOf q) (1329)) (countLit q [-57]) (countLit q [-60, -62]) (count1328 q) 1 1 (meaningNeg57 q) (meaning1326 q) (meaning1329 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1326 = false ∨ valuation q 1329 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1327 = false ∨ valuationOf q 1330 = true := by
  have hs : count1328 q = (countLit q [-57]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60, -62])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (1327)) (literal (valuationOf q) (1330)) (countLit q [-57]) (countLit q [-60, -62]) (count1328 q) 1 2 (meaningNeg57 q) (meaning1327 q) (meaning1330 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1327 = false ∨ valuation q 1330 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1331 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_right (literal (valuationOf q) (1328)) (literal (valuationOf q) (1331)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 1 (meaning1328 q) (meaning1331 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1331 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1332 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_right (literal (valuationOf q) (1329)) (literal (valuationOf q) (1332)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 2 (meaning1329 q) (meaning1332 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1332 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1333 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_right (literal (valuationOf q) (1330)) (literal (valuationOf q) (1333)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 3 (meaning1330 q) (meaning1333 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1333 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1331 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_left (literal (valuationOf q) (1323)) (literal (valuationOf q) (1331)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 1 (meaning1323 q) (meaning1331 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1331 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1332 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1323)) (literal (valuationOf q) (1328)) (literal (valuationOf q) (1332)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 1 1 (meaning1323 q) (meaning1328 q) (meaning1332 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1328 = false ∨ valuation q 1332 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1329 = false ∨ valuationOf q 1333 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1323)) (literal (valuationOf q) (1329)) (literal (valuationOf q) (1333)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 1 2 (meaning1323 q) (meaning1329 q) (meaning1333 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1329 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1329 = false ∨ valuation q 1333 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1334 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1323)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1334)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 1 3 (meaning1323 q) (meaning1330 q) (meaning1334 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1330 = false ∨ valuation q 1334 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1332 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_left (literal (valuationOf q) (1324)) (literal (valuationOf q) (1332)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 2 (meaning1324 q) (meaning1332 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1332 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1333 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1324)) (literal (valuationOf q) (1328)) (literal (valuationOf q) (1333)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 2 1 (meaning1324 q) (meaning1328 q) (meaning1333 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1328 = false ∨ valuation q 1333 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1329 = false ∨ valuationOf q 1334 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1324)) (literal (valuationOf q) (1329)) (literal (valuationOf q) (1334)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 2 2 (meaning1324 q) (meaning1329 q) (meaning1334 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1329 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1329 = false ∨ valuation q 1334 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1335 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1324)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1335)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 2 3 (meaning1324 q) (meaning1330 q) (meaning1335 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1330 = false ∨ valuation q 1335 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1325 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1334 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1325)) (literal (valuationOf q) (1328)) (literal (valuationOf q) (1334)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 3 1 (meaning1325 q) (meaning1328 q) (meaning1334 q) hs
  change valuationOf q 1325 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1325 = false ∨ valuation q 1328 = false ∨ valuation q 1334 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1325 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1336 = true := by
  have hs : count1331 q = (countLit q [-52, -54, -55]) + (countLit q [-57, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -54, -55]) (l₂ := [-57, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1325)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1336)) (countLit q [-52, -54, -55]) (countLit q [-57, -60, -62]) (count1331 q) 3 3 (meaning1325 q) (meaning1330 q) (meaning1336 q) hs
  change valuationOf q 1325 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1325 = false ∨ valuation q 1330 = false ∨ valuation q 1336 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E174.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112174
