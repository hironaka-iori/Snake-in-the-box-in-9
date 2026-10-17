import E112190Semantics
import B112E190Inputs
namespace Snake9.Regrowth.E112190
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1311 = true := by
  have hs : count1310 q = (countLit q [-21]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1311)) (countLit q [-21]) (countLit q [-24]) (count1310 q) 1 1 (meaningNeg21 q) (meaningNeg24 q) (meaning1311 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 24 = true ∨ valuation q 1311 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1312 = true := by
  have hs : count1312 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1312)) (countLit q [-25]) (countLit q [-27]) (count1312 q) 1 (meaningNeg25 q) (meaning1312 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1312 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1314 = true := by
  have hs : count1314 q = (countLit q [-21, -24]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -27])
  have hm := merge_right (literal (valuationOf q) (1312)) (literal (valuationOf q) (1314)) (countLit q [-21, -24]) (countLit q [-25, -27]) (count1314 q) 1 (meaning1312 q) (meaning1314 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1314 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1314 = true := by
  have hs : count1314 q = (countLit q [-21, -24]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -27])
  have hm := merge_left (literal (valuationOf q) (1310)) (literal (valuationOf q) (1314)) (countLit q [-21, -24]) (countLit q [-25, -27]) (count1314 q) 1 (meaning1310 q) (meaning1314 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1314 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1315 = true := by
  have hs : count1314 q = (countLit q [-21, -24]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (1310)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1315)) (countLit q [-21, -24]) (countLit q [-25, -27]) (count1314 q) 1 1 (meaning1310 q) (meaning1312 q) (meaning1315 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1312 = false ∨ valuation q 1315 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1315 = true := by
  have hs : count1314 q = (countLit q [-21, -24]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -27])
  have hm := merge_left (literal (valuationOf q) (1311)) (literal (valuationOf q) (1315)) (countLit q [-21, -24]) (countLit q [-25, -27]) (count1314 q) 2 (meaning1311 q) (meaning1315 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1315 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 1314 = false ∨ valuationOf q 1318 = true := by
  have hs : count1318 q = (countLit q [-13, -15, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1314)) (literal (valuationOf q) (1318)) (countLit q [-13, -15, -19]) (countLit q [-21, -24, -25, -27]) (count1318 q) 1 (meaning1314 q) (meaning1318 q) hs
  change valuationOf q 1314 = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 1314 = false ∨ valuation q 1318 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 1315 = false ∨ valuationOf q 1319 = true := by
  have hs : count1318 q = (countLit q [-13, -15, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1315)) (literal (valuationOf q) (1319)) (countLit q [-13, -15, -19]) (countLit q [-21, -24, -25, -27]) (count1318 q) 2 (meaning1315 q) (meaning1319 q) hs
  change valuationOf q 1315 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 1315 = false ∨ valuation q 1319 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 1307 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1319 = true := by
  have hs : count1318 q = (countLit q [-13, -15, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1307)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1319)) (countLit q [-13, -15, -19]) (countLit q [-21, -24, -25, -27]) (count1318 q) 1 1 (meaning1307 q) (meaning1314 q) (meaning1319 q) hs
  change valuationOf q 1307 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 1307 = false ∨ valuation q 1314 = false ∨ valuation q 1319 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 1299 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1327 = true := by
  have hs : count1325 q = (countLit q [-2, -4, -5, -7, -10, -12]) + (countLit q [-13, -15, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12]) (l₂ := [-13, -15, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1299)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1327)) (countLit q [-2, -4, -5, -7, -10, -12]) (countLit q [-13, -15, -19, -21, -24, -25, -27]) (count1325 q) 1 2 (meaning1299 q) (meaning1319 q) (meaning1327 q) hs
  change valuationOf q 1299 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 1299 = false ∨ valuation q 1319 = false ∨ valuation q 1327 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 1300 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1327 = true := by
  have hs : count1325 q = (countLit q [-2, -4, -5, -7, -10, -12]) + (countLit q [-13, -15, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12]) (l₂ := [-13, -15, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1300)) (literal (valuationOf q) (1318)) (literal (valuationOf q) (1327)) (countLit q [-2, -4, -5, -7, -10, -12]) (countLit q [-13, -15, -19, -21, -24, -25, -27]) (count1325 q) 2 1 (meaning1300 q) (meaning1318 q) (meaning1327 q) hs
  change valuationOf q 1300 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 1300 = false ∨ valuation q 1318 = false ∨ valuation q 1327 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1338)) (countLit q [-32]) (countLit q [-33]) (count1338 q) 1 (meaningNeg32 q) (meaning1338 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1338 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-30]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -33])
  have hm := merge_right (literal (valuationOf q) (1338)) (literal (valuationOf q) (1340)) (countLit q [-30]) (countLit q [-32, -33]) (count1340 q) 1 (meaning1338 q) (meaning1340 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1340 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-30]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -33])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1340)) (countLit q [-30]) (countLit q [-32, -33]) (count1340 q) 1 (meaningNeg30 q) (meaning1340 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1340 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1338 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-30]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -33])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1341)) (countLit q [-30]) (countLit q [-32, -33]) (count1340 q) 1 1 (meaningNeg30 q) (meaning1338 q) (meaning1341 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1338 = false ∨ valuation q 1341 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1343)) (countLit q [-38]) (countLit q [-40]) (count1343 q) 1 (meaningNeg40 q) (meaning1343 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1343 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1343)) (countLit q [-38]) (countLit q [-40]) (count1343 q) 1 (meaningNeg38 q) (meaning1343 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1343 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1345 = true := by
  have hs : count1345 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1343)) (literal (valuationOf q) (1345)) (countLit q [-35]) (countLit q [-38, -40]) (count1345 q) 1 (meaning1343 q) (meaning1345 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1345 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1345 = true := by
  have hs : count1345 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1345)) (countLit q [-35]) (countLit q [-38, -40]) (count1345 q) 1 (meaningNeg35 q) (meaning1345 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1345 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1348 = true := by
  have hs : count1348 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1345)) (literal (valuationOf q) (1348)) (countLit q [-30, -32, -33]) (countLit q [-35, -38, -40]) (count1348 q) 1 (meaning1345 q) (meaning1348 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1348 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1348 = true := by
  have hs : count1348 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1340)) (literal (valuationOf q) (1348)) (countLit q [-30, -32, -33]) (countLit q [-35, -38, -40]) (count1348 q) 1 (meaning1340 q) (meaning1348 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1348 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1349 = true := by
  have hs : count1348 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1340)) (literal (valuationOf q) (1345)) (literal (valuationOf q) (1349)) (countLit q [-30, -32, -33]) (countLit q [-35, -38, -40]) (count1348 q) 1 1 (meaning1340 q) (meaning1345 q) (meaning1349 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1345 = false ∨ valuation q 1349 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1349 = true := by
  have hs : count1348 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1341)) (literal (valuationOf q) (1349)) (countLit q [-30, -32, -33]) (countLit q [-35, -38, -40]) (count1348 q) 2 (meaning1341 q) (meaning1349 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1349 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1354)) (countLit q [-43]) (countLit q [-46]) (count1354 q) 1 (meaningNeg46 q) (meaning1354 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1354 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43, -46])
  have hm := merge_right (literal (valuationOf q) (1354)) (literal (valuationOf q) (1356)) (countLit q [-41]) (countLit q [-43, -46]) (count1356 q) 1 (meaning1354 q) (meaning1356 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1356 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43, -46])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1356)) (countLit q [-41]) (countLit q [-43, -46]) (count1356 q) 1 (meaningNeg41 q) (meaning1356 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1356 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1354 = false ∨ valuationOf q 1357 = true := by
  have hs : count1356 q = (countLit q [-41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1357)) (countLit q [-41]) (countLit q [-43, -46]) (count1356 q) 1 1 (meaningNeg41 q) (meaning1354 q) (meaning1357 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1354 = false ∨ valuation q 1357 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1359 = true := by
  have hs : count1359 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1359)) (countLit q [-48]) (countLit q [-49]) (count1359 q) 1 (meaningNeg49 q) (meaning1359 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1359 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1359 = true := by
  have hs : count1359 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1359)) (countLit q [-48]) (countLit q [-49]) (count1359 q) 1 (meaningNeg48 q) (meaning1359 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1359 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 49 = true ∨ valuationOf q 1360 = true := by
  have hs : count1359 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (1360)) (countLit q [-48]) (countLit q [-49]) (count1359 q) 1 1 (meaningNeg48 q) (meaningNeg49 q) (meaning1360 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 1360 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1361 = true := by
  have hs : count1361 q = (countLit q [-51]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1361)) (countLit q [-51]) (countLit q [-54]) (count1361 q) 1 (meaningNeg54 q) (meaning1361 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1361 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1361 = true := by
  have hs : count1361 q = (countLit q [-51]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (1361)) (countLit q [-51]) (countLit q [-54]) (count1361 q) 1 (meaningNeg51 q) (meaning1361 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1361 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E190.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112190
