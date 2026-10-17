import E112234Semantics
import B112E234Inputs
namespace Snake9.Regrowth.E112234
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 1224 = false ∨ valuationOf q 1270 = false ∨ valuationOf q 1284 = true := by
  have hs : count1280 q = (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) + (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (l₂ := [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1224)) (literal (valuationOf q) (1270)) (literal (valuationOf q) (1284)) (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (count1280 q) 3 2 (meaning1224 q) (meaning1270 q) (meaning1284 q) hs
  change valuationOf q 1224 = false ∨ valuationOf q 1270 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 1224 = false ∨ valuation q 1270 = false ∨ valuation q 1284 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 1224 = false ∨ valuationOf q 1271 = false ∨ valuationOf q 1285 = true := by
  have hs : count1280 q = (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) + (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (l₂ := [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1224)) (literal (valuationOf q) (1271)) (literal (valuationOf q) (1285)) (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (count1280 q) 3 3 (meaning1224 q) (meaning1271 q) (meaning1285 q) hs
  change valuationOf q 1224 = false ∨ valuationOf q 1271 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 1224 = false ∨ valuation q 1271 = false ∨ valuation q 1285 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 1224 = false ∨ valuationOf q 1272 = false ∨ valuationOf q 1286 = true := by
  have hs : count1280 q = (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) + (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (l₂ := [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1224)) (literal (valuationOf q) (1272)) (literal (valuationOf q) (1286)) (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (count1280 q) 3 4 (meaning1224 q) (meaning1272 q) (meaning1286 q) hs
  change valuationOf q 1224 = false ∨ valuationOf q 1272 = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 1224 = false ∨ valuation q 1272 = false ∨ valuation q 1286 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 1225 = false ∨ valuationOf q 1270 = false ∨ valuationOf q 1285 = true := by
  have hs : count1280 q = (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) + (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (l₂ := [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1225)) (literal (valuationOf q) (1270)) (literal (valuationOf q) (1285)) (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (count1280 q) 4 2 (meaning1225 q) (meaning1270 q) (meaning1285 q) hs
  change valuationOf q 1225 = false ∨ valuationOf q 1270 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 1225 = false ∨ valuation q 1270 = false ∨ valuation q 1285 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 1225 = false ∨ valuationOf q 1271 = false ∨ valuationOf q 1286 = true := by
  have hs : count1280 q = (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) + (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (l₂ := [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1225)) (literal (valuationOf q) (1271)) (literal (valuationOf q) (1286)) (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (count1280 q) 4 3 (meaning1225 q) (meaning1271 q) (meaning1286 q) hs
  change valuationOf q 1225 = false ∨ valuationOf q 1271 = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 1225 = false ∨ valuation q 1271 = false ∨ valuation q 1286 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 1226 = false ∨ valuationOf q 1269 = false ∨ valuationOf q 1285 = true := by
  have hs : count1280 q = (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) + (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (l₂ := [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1226)) (literal (valuationOf q) (1269)) (literal (valuationOf q) (1285)) (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (count1280 q) 5 1 (meaning1226 q) (meaning1269 q) (meaning1285 q) hs
  change valuationOf q 1226 = false ∨ valuationOf q 1269 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 1226 = false ∨ valuation q 1269 = false ∨ valuation q 1285 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 1226 = false ∨ valuationOf q 1270 = false ∨ valuationOf q 1286 = true := by
  have hs : count1280 q = (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) + (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (l₂ := [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1226)) (literal (valuationOf q) (1270)) (literal (valuationOf q) (1286)) (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (count1280 q) 5 2 (meaning1226 q) (meaning1270 q) (meaning1286 q) hs
  change valuationOf q 1226 = false ∨ valuationOf q 1270 = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 1226 = false ∨ valuation q 1270 = false ∨ valuation q 1286 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1296 = true := by
  have hs : count1296 q = (countLit q [-60]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1296)) (countLit q [-60]) (countLit q [-61]) (count1296 q) 1 (meaningNeg60 q) (meaning1296 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1296 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1298 = true := by
  have hs : count1298 q = (countLit q [-58]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60, -61])
  have hm := merge_right (literal (valuationOf q) (1296)) (literal (valuationOf q) (1298)) (countLit q [-58]) (countLit q [-60, -61]) (count1298 q) 1 (meaning1296 q) (meaning1298 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1298 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 1298 = false ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-52, -53, -55]) + (countLit q [-58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55]) (l₂ := [-58, -60, -61])
  have hm := merge_right (literal (valuationOf q) (1298)) (literal (valuationOf q) (1301)) (countLit q [-52, -53, -55]) (countLit q [-58, -60, -61]) (count1301 q) 1 (meaning1298 q) (meaning1301 q) hs
  change valuationOf q 1298 = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 1298 = false ∨ valuation q 1301 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1307 = true := by
  have hs : count1307 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1307)) (countLit q [-65]) (countLit q [-67]) (count1307 q) 1 (meaningNeg65 q) (meaning1307 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1307 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1307 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 1307 = false ∨ valuationOf q 1309 = true := by
  have hs : count1309 q = (countLit q [-63]) + (countLit q [-65, -67]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -67])
  have hm := merge_right (literal (valuationOf q) (1307)) (literal (valuationOf q) (1309)) (countLit q [-63]) (countLit q [-65, -67]) (count1309 q) 1 (meaning1307 q) (meaning1309 q) hs
  change valuationOf q 1307 = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 1307 = false ∨ valuation q 1309 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1309 = true := by
  have hs : count1309 q = (countLit q [-63]) + (countLit q [-65, -67]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -67])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1309)) (countLit q [-63]) (countLit q [-65, -67]) (count1309 q) 1 (meaningNeg63 q) (meaning1309 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1309 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1312 = true := by
  have hs : count1312 q = (countLit q [-68]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1312)) (countLit q [-68]) (countLit q [-70]) (count1312 q) 1 (meaningNeg68 q) (meaning1312 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1312 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1314 = true := by
  have hs : count1314 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1314)) (countLit q [-74]) (countLit q [-76]) (count1314 q) 1 (meaningNeg76 q) (meaning1314 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1314 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1315 = true := by
  have hs : count1314 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1315)) (countLit q [-74]) (countLit q [-76]) (count1314 q) 1 1 (meaningNeg74 q) (meaningNeg76 q) (meaning1315 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 1315 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1316 = true := by
  have hs : count1316 q = (countLit q [-68, -70]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-68, -70]) (l₂ := [-74, -76])
  have hm := merge_left (literal (valuationOf q) (1312)) (literal (valuationOf q) (1316)) (countLit q [-68, -70]) (countLit q [-74, -76]) (count1316 q) 1 (meaning1312 q) (meaning1316 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1316 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1317 = true := by
  have hs : count1316 q = (countLit q [-68, -70]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-68, -70]) (l₂ := [-74, -76])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1317)) (countLit q [-68, -70]) (countLit q [-74, -76]) (count1316 q) 1 1 (meaning1312 q) (meaning1314 q) (meaning1317 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1314 = false ∨ valuation q 1317 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1315 = false ∨ valuationOf q 1318 = true := by
  have hs : count1316 q = (countLit q [-68, -70]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-68, -70]) (l₂ := [-74, -76])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1315)) (literal (valuationOf q) (1318)) (countLit q [-68, -70]) (countLit q [-74, -76]) (count1316 q) 1 2 (meaning1312 q) (meaning1315 q) (meaning1318 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1315 = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1315 = false ∨ valuation q 1318 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 1316 = false ∨ valuationOf q 1320 = true := by
  have hs : count1320 q = (countLit q [-63, -65, -67]) + (countLit q [-68, -70, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -67]) (l₂ := [-68, -70, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1316)) (literal (valuationOf q) (1320)) (countLit q [-63, -65, -67]) (countLit q [-68, -70, -74, -76]) (count1320 q) 1 (meaning1316 q) (meaning1320 q) hs
  change valuationOf q 1316 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 1316 = false ∨ valuation q 1320 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1321 = true := by
  have hs : count1320 q = (countLit q [-63, -65, -67]) + (countLit q [-68, -70, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -67]) (l₂ := [-68, -70, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1317)) (literal (valuationOf q) (1321)) (countLit q [-63, -65, -67]) (countLit q [-68, -70, -74, -76]) (count1320 q) 2 (meaning1317 q) (meaning1321 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1321 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 1318 = false ∨ valuationOf q 1322 = true := by
  have hs : count1320 q = (countLit q [-63, -65, -67]) + (countLit q [-68, -70, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -67]) (l₂ := [-68, -70, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1318)) (literal (valuationOf q) (1322)) (countLit q [-63, -65, -67]) (countLit q [-68, -70, -74, -76]) (count1320 q) 3 (meaning1318 q) (meaning1322 q) hs
  change valuationOf q 1318 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 1318 = false ∨ valuation q 1322 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1321 = true := by
  have hs : count1320 q = (countLit q [-63, -65, -67]) + (countLit q [-68, -70, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -67]) (l₂ := [-68, -70, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1309)) (literal (valuationOf q) (1316)) (literal (valuationOf q) (1321)) (countLit q [-63, -65, -67]) (countLit q [-68, -70, -74, -76]) (count1320 q) 1 1 (meaning1309 q) (meaning1316 q) (meaning1321 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1316 = false ∨ valuation q 1321 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1322 = true := by
  have hs : count1320 q = (countLit q [-63, -65, -67]) + (countLit q [-68, -70, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -67]) (l₂ := [-68, -70, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1309)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1322)) (countLit q [-63, -65, -67]) (countLit q [-68, -70, -74, -76]) (count1320 q) 1 2 (meaning1309 q) (meaning1317 q) (meaning1322 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1317 = false ∨ valuation q 1322 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-52, -53, -55, -58, -60, -61]) + (countLit q [-63, -65, -67, -68, -70, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -58, -60, -61]) (l₂ := [-63, -65, -67, -68, -70, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1321)) (literal (valuationOf q) (1328)) (countLit q [-52, -53, -55, -58, -60, -61]) (countLit q [-63, -65, -67, -68, -70, -74, -76]) (count1327 q) 2 (meaning1321 q) (meaning1328 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1328 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1329 = true := by
  have hs : count1327 q = (countLit q [-52, -53, -55, -58, -60, -61]) + (countLit q [-63, -65, -67, -68, -70, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -58, -60, -61]) (l₂ := [-63, -65, -67, -68, -70, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1322)) (literal (valuationOf q) (1329)) (countLit q [-52, -53, -55, -58, -60, -61]) (countLit q [-63, -65, -67, -68, -70, -74, -76]) (count1327 q) 3 (meaning1322 q) (meaning1329 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1329 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-52, -53, -55, -58, -60, -61]) + (countLit q [-63, -65, -67, -68, -70, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -58, -60, -61]) (l₂ := [-63, -65, -67, -68, -70, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1328)) (countLit q [-52, -53, -55, -58, -60, -61]) (countLit q [-63, -65, -67, -68, -70, -74, -76]) (count1327 q) 1 1 (meaning1301 q) (meaning1320 q) (meaning1328 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1320 = false ∨ valuation q 1328 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1329 = true := by
  have hs : count1327 q = (countLit q [-52, -53, -55, -58, -60, -61]) + (countLit q [-63, -65, -67, -68, -70, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -58, -60, -61]) (l₂ := [-63, -65, -67, -68, -70, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1329)) (countLit q [-52, -53, -55, -58, -60, -61]) (countLit q [-63, -65, -67, -68, -70, -74, -76]) (count1327 q) 1 2 (meaning1301 q) (meaning1321 q) (meaning1329 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1321 = false ∨ valuation q 1329 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1338)) (countLit q [-78]) (countLit q [-81]) (count1338 q) 1 (meaningNeg81 q) (meaning1338 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1338 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1338)) (countLit q [-78]) (countLit q [-81]) (count1338 q) 1 (meaningNeg78 q) (meaning1338 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1338 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1339 = true := by
  have hs : count1338 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1339)) (countLit q [-78]) (countLit q [-81]) (count1338 q) 1 1 (meaningNeg78 q) (meaningNeg81 q) (meaning1339 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 81 = true ∨ valuation q 1339 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78, -81])
  have hm := merge_right (literal (valuationOf q) (1338)) (literal (valuationOf q) (1340)) (countLit q [-77]) (countLit q [-78, -81]) (count1340 q) 1 (meaning1338 q) (meaning1340 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1340 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E234.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112234
