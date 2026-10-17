import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1296 = true := by
  have hs : count1296 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1296)) (countLit q [-8]) (countLit q [-11]) (count1296 q) 1 (meaningNeg8 q) (meaning1296 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1296 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1298 = true := by
  have hs : count1298 q = (countLit q [-7]) + (countLit q [-8, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-8, -11])
  have hm := merge_right (literal (valuationOf q) (1296)) (literal (valuationOf q) (1298)) (countLit q [-7]) (countLit q [-8, -11]) (count1298 q) 1 (meaning1296 q) (meaning1298 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1298 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1296 = false ∨ valuationOf q 1299 = true := by
  have hs : count1298 q = (countLit q [-7]) + (countLit q [-8, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-8, -11])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1299)) (countLit q [-7]) (countLit q [-8, -11]) (count1298 q) 1 1 (meaningNeg7 q) (meaning1296 q) (meaning1299 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1296 = false ∨ valuation q 1299 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 1298 = false ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -8, -11])
  have hm := merge_right (literal (valuationOf q) (1298)) (literal (valuationOf q) (1301)) (countLit q [-2, -3, -5]) (countLit q [-7, -8, -11]) (count1301 q) 1 (meaning1298 q) (meaning1301 q) hs
  change valuationOf q 1298 = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 1298 = false ∨ valuation q 1301 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 1299 = false ∨ valuationOf q 1302 = true := by
  have hs : count1301 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -8, -11])
  have hm := merge_right (literal (valuationOf q) (1299)) (literal (valuationOf q) (1302)) (countLit q [-2, -3, -5]) (countLit q [-7, -8, -11]) (count1301 q) 2 (meaning1299 q) (meaning1302 q) hs
  change valuationOf q 1299 = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 1299 = false ∨ valuation q 1302 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1302 = true := by
  have hs : count1301 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1298)) (literal (valuationOf q) (1302)) (countLit q [-2, -3, -5]) (countLit q [-7, -8, -11]) (count1301 q) 1 1 (meaning1293 q) (meaning1298 q) (meaning1302 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1298 = false ∨ valuation q 1302 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1303 = true := by
  have hs : count1301 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1299)) (literal (valuationOf q) (1303)) (countLit q [-2, -3, -5]) (countLit q [-7, -8, -11]) (count1301 q) 1 2 (meaning1293 q) (meaning1299 q) (meaning1303 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1299 = false ∨ valuation q 1303 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1303 = true := by
  have hs : count1301 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1294)) (literal (valuationOf q) (1298)) (literal (valuationOf q) (1303)) (countLit q [-2, -3, -5]) (countLit q [-7, -8, -11]) (count1301 q) 2 1 (meaning1294 q) (meaning1298 q) (meaning1303 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1298 = false ∨ valuation q 1303 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1304 = true := by
  have hs : count1301 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1294)) (literal (valuationOf q) (1299)) (literal (valuationOf q) (1304)) (countLit q [-2, -3, -5]) (countLit q [-7, -8, -11]) (count1301 q) 2 2 (meaning1294 q) (meaning1299 q) (meaning1304 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1299 = false ∨ valuation q 1304 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 1295 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1304 = true := by
  have hs : count1301 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1295)) (literal (valuationOf q) (1298)) (literal (valuationOf q) (1304)) (countLit q [-2, -3, -5]) (countLit q [-7, -8, -11]) (count1301 q) 3 1 (meaning1295 q) (meaning1298 q) (meaning1304 q) hs
  change valuationOf q 1295 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 1295 = false ∨ valuation q 1298 = false ∨ valuation q 1304 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1307 = true := by
  have hs : count1307 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1307)) (countLit q [-14]) (countLit q [-17]) (count1307 q) 1 (meaningNeg17 q) (meaning1307 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1307 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1307 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1307 = true := by
  have hs : count1307 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1307)) (countLit q [-14]) (countLit q [-17]) (count1307 q) 1 (meaningNeg14 q) (meaning1307 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1307 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1307 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 17 = true ∨ valuationOf q 1308 = true := by
  have hs : count1307 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (1308)) (countLit q [-14]) (countLit q [-17]) (count1307 q) 1 1 (meaningNeg14 q) (meaningNeg17 q) (meaning1308 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 1308 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 1307 = false ∨ valuationOf q 1309 = true := by
  have hs : count1309 q = (countLit q [-13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -17])
  have hm := merge_right (literal (valuationOf q) (1307)) (literal (valuationOf q) (1309)) (countLit q [-13]) (countLit q [-14, -17]) (count1309 q) 1 (meaning1307 q) (meaning1309 q) hs
  change valuationOf q 1307 = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 1307 = false ∨ valuation q 1309 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1310 = true := by
  have hs : count1309 q = (countLit q [-13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -17])
  have hm := merge_right (literal (valuationOf q) (1308)) (literal (valuationOf q) (1310)) (countLit q [-13]) (countLit q [-14, -17]) (count1309 q) 2 (meaning1308 q) (meaning1310 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1310 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1309 = true := by
  have hs : count1309 q = (countLit q [-13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -17])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1309)) (countLit q [-13]) (countLit q [-14, -17]) (count1309 q) 1 (meaningNeg13 q) (meaning1309 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1309 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1312 = true := by
  have hs : count1312 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1312)) (countLit q [-19]) (countLit q [-21]) (count1312 q) 1 (meaningNeg21 q) (meaning1312 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1312 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1312 = true := by
  have hs : count1312 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1312)) (countLit q [-19]) (countLit q [-21]) (count1312 q) 1 (meaningNeg19 q) (meaning1312 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1312 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 21 = true ∨ valuationOf q 1313 = true := by
  have hs : count1312 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (1313)) (countLit q [-19]) (countLit q [-21]) (count1312 q) 1 1 (meaningNeg19 q) (meaningNeg21 q) (meaning1313 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 1313 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1314 = true := by
  have hs : count1314 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1314)) (countLit q [-22]) (countLit q [-24]) (count1314 q) 1 (meaningNeg24 q) (meaning1314 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1314 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1314 = true := by
  have hs : count1314 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1314)) (countLit q [-22]) (countLit q [-24]) (count1314 q) 1 (meaningNeg22 q) (meaning1314 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1314 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 1314 = false ∨ valuationOf q 1316 = true := by
  have hs : count1316 q = (countLit q [-19, -21]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-19, -21]) (l₂ := [-22, -24])
  have hm := merge_right (literal (valuationOf q) (1314)) (literal (valuationOf q) (1316)) (countLit q [-19, -21]) (countLit q [-22, -24]) (count1316 q) 1 (meaning1314 q) (meaning1316 q) hs
  change valuationOf q 1314 = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 1314 = false ∨ valuation q 1316 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1316 = true := by
  have hs : count1316 q = (countLit q [-19, -21]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-19, -21]) (l₂ := [-22, -24])
  have hm := merge_left (literal (valuationOf q) (1312)) (literal (valuationOf q) (1316)) (countLit q [-19, -21]) (countLit q [-22, -24]) (count1316 q) 1 (meaning1312 q) (meaning1316 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1316 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1317 = true := by
  have hs : count1316 q = (countLit q [-19, -21]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-19, -21]) (l₂ := [-22, -24])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1317)) (countLit q [-19, -21]) (countLit q [-22, -24]) (count1316 q) 1 1 (meaning1312 q) (meaning1314 q) (meaning1317 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1314 = false ∨ valuation q 1317 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1317 = true := by
  have hs : count1316 q = (countLit q [-19, -21]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-19, -21]) (l₂ := [-22, -24])
  have hm := merge_left (literal (valuationOf q) (1313)) (literal (valuationOf q) (1317)) (countLit q [-19, -21]) (countLit q [-22, -24]) (count1316 q) 2 (meaning1313 q) (meaning1317 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1317 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 1316 = false ∨ valuationOf q 1320 = true := by
  have hs : count1320 q = (countLit q [-13, -14, -17]) + (countLit q [-19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-19, -21, -22, -24])
  have hm := merge_right (literal (valuationOf q) (1316)) (literal (valuationOf q) (1320)) (countLit q [-13, -14, -17]) (countLit q [-19, -21, -22, -24]) (count1320 q) 1 (meaning1316 q) (meaning1320 q) hs
  change valuationOf q 1316 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 1316 = false ∨ valuation q 1320 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1321 = true := by
  have hs : count1320 q = (countLit q [-13, -14, -17]) + (countLit q [-19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-19, -21, -22, -24])
  have hm := merge_right (literal (valuationOf q) (1317)) (literal (valuationOf q) (1321)) (countLit q [-13, -14, -17]) (countLit q [-19, -21, -22, -24]) (count1320 q) 2 (meaning1317 q) (meaning1321 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1321 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1320 = true := by
  have hs : count1320 q = (countLit q [-13, -14, -17]) + (countLit q [-19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-19, -21, -22, -24])
  have hm := merge_left (literal (valuationOf q) (1309)) (literal (valuationOf q) (1320)) (countLit q [-13, -14, -17]) (countLit q [-19, -21, -22, -24]) (count1320 q) 1 (meaning1309 q) (meaning1320 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1320 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1321 = true := by
  have hs : count1320 q = (countLit q [-13, -14, -17]) + (countLit q [-19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1309)) (literal (valuationOf q) (1316)) (literal (valuationOf q) (1321)) (countLit q [-13, -14, -17]) (countLit q [-19, -21, -22, -24]) (count1320 q) 1 1 (meaning1309 q) (meaning1316 q) (meaning1321 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1316 = false ∨ valuation q 1321 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1322 = true := by
  have hs : count1320 q = (countLit q [-13, -14, -17]) + (countLit q [-19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1309)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1322)) (countLit q [-13, -14, -17]) (countLit q [-19, -21, -22, -24]) (count1320 q) 1 2 (meaning1309 q) (meaning1317 q) (meaning1322 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1317 = false ∨ valuation q 1322 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1321 = true := by
  have hs : count1320 q = (countLit q [-13, -14, -17]) + (countLit q [-19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-19, -21, -22, -24])
  have hm := merge_left (literal (valuationOf q) (1310)) (literal (valuationOf q) (1321)) (countLit q [-13, -14, -17]) (countLit q [-19, -21, -22, -24]) (count1320 q) 2 (meaning1310 q) (meaning1321 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1321 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1327 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_left (literal (valuationOf q) (1301)) (literal (valuationOf q) (1327)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 1 (meaning1301 q) (meaning1327 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1327 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E166.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112166
