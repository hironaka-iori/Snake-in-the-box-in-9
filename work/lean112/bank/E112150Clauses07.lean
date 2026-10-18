import E112150Semantics
import B112E150Inputs
namespace Snake9.Regrowth.E112150
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1312 = true := by
  have hs : count1311 q = (countLit q [-28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -33])
  have hm := merge_right (literal (valuationOf q) (1310)) (literal (valuationOf q) (1312)) (countLit q [-28]) (countLit q [-30, -33]) (count1311 q) 2 (meaning1310 q) (meaning1312 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1312 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -33])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1311)) (countLit q [-28]) (countLit q [-30, -33]) (count1311 q) 1 (meaningNeg28 q) (meaning1311 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1311 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1309 = false ∨ valuationOf q 1312 = true := by
  have hs : count1311 q = (countLit q [-28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -33])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (1309)) (literal (valuationOf q) (1312)) (countLit q [-28]) (countLit q [-30, -33]) (count1311 q) 1 1 (meaningNeg28 q) (meaning1309 q) (meaning1312 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1309 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1309 = false ∨ valuation q 1312 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1314 = true := by
  have hs : count1314 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (1314)) (countLit q [-37]) (countLit q [-38]) (count1314 q) 1 (meaningNeg38 q) (meaning1314 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1314 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1314 = true := by
  have hs : count1314 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1314)) (countLit q [-37]) (countLit q [-38]) (count1314 q) 1 (meaningNeg37 q) (meaning1314 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1314 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 38 = true ∨ valuationOf q 1315 = true := by
  have hs : count1314 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (1315)) (countLit q [-37]) (countLit q [-38]) (count1314 q) 1 1 (meaningNeg37 q) (meaningNeg38 q) (meaning1315 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 1315 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 1314 = false ∨ valuationOf q 1316 = true := by
  have hs : count1316 q = (countLit q [-35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37, -38])
  have hm := merge_right (literal (valuationOf q) (1314)) (literal (valuationOf q) (1316)) (countLit q [-35]) (countLit q [-37, -38]) (count1316 q) 1 (meaning1314 q) (meaning1316 q) hs
  change valuationOf q 1314 = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 1314 = false ∨ valuation q 1316 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 1315 = false ∨ valuationOf q 1317 = true := by
  have hs : count1316 q = (countLit q [-35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37, -38])
  have hm := merge_right (literal (valuationOf q) (1315)) (literal (valuationOf q) (1317)) (countLit q [-35]) (countLit q [-37, -38]) (count1316 q) 2 (meaning1315 q) (meaning1317 q) hs
  change valuationOf q 1315 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 1315 = false ∨ valuation q 1317 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1316 = true := by
  have hs : count1316 q = (countLit q [-35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37, -38])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1316)) (countLit q [-35]) (countLit q [-37, -38]) (count1316 q) 1 (meaningNeg35 q) (meaning1316 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1316 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1314 = false ∨ valuationOf q 1317 = true := by
  have hs : count1316 q = (countLit q [-35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1317)) (countLit q [-35]) (countLit q [-37, -38]) (count1316 q) 1 1 (meaningNeg35 q) (meaning1314 q) (meaning1317 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1314 = false ∨ valuation q 1317 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 1316 = false ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-28, -30, -33]) + (countLit q [-35, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-35, -37, -38])
  have hm := merge_right (literal (valuationOf q) (1316)) (literal (valuationOf q) (1319)) (countLit q [-28, -30, -33]) (countLit q [-35, -37, -38]) (count1319 q) 1 (meaning1316 q) (meaning1319 q) hs
  change valuationOf q 1316 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 1316 = false ∨ valuation q 1319 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-28, -30, -33]) + (countLit q [-35, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-35, -37, -38])
  have hm := merge_right (literal (valuationOf q) (1317)) (literal (valuationOf q) (1320)) (countLit q [-28, -30, -33]) (countLit q [-35, -37, -38]) (count1319 q) 2 (meaning1317 q) (meaning1320 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1320 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-28, -30, -33]) + (countLit q [-35, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-35, -37, -38])
  have hm := merge_left (literal (valuationOf q) (1311)) (literal (valuationOf q) (1319)) (countLit q [-28, -30, -33]) (countLit q [-35, -37, -38]) (count1319 q) 1 (meaning1311 q) (meaning1319 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1319 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-28, -30, -33]) + (countLit q [-35, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-35, -37, -38])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1316)) (literal (valuationOf q) (1320)) (countLit q [-28, -30, -33]) (countLit q [-35, -37, -38]) (count1319 q) 1 1 (meaning1311 q) (meaning1316 q) (meaning1320 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1316 = false ∨ valuation q 1320 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1321 = true := by
  have hs : count1319 q = (countLit q [-28, -30, -33]) + (countLit q [-35, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-35, -37, -38])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1321)) (countLit q [-28, -30, -33]) (countLit q [-35, -37, -38]) (count1319 q) 1 2 (meaning1311 q) (meaning1317 q) (meaning1321 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1317 = false ∨ valuation q 1321 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-28, -30, -33]) + (countLit q [-35, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-35, -37, -38])
  have hm := merge_left (literal (valuationOf q) (1312)) (literal (valuationOf q) (1320)) (countLit q [-28, -30, -33]) (countLit q [-35, -37, -38]) (count1319 q) 2 (meaning1312 q) (meaning1320 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1320 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1321 = true := by
  have hs : count1319 q = (countLit q [-28, -30, -33]) + (countLit q [-35, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33]) (l₂ := [-35, -37, -38])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1316)) (literal (valuationOf q) (1321)) (countLit q [-28, -30, -33]) (countLit q [-35, -37, -38]) (count1319 q) 2 1 (meaning1312 q) (meaning1316 q) (meaning1321 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1316 = false ∨ valuation q 1321 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1325 = true := by
  have hs : count1325 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1325)) (countLit q [-42]) (countLit q [-44]) (count1325 q) 1 (meaningNeg44 q) (meaning1325 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1325 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1325 = true := by
  have hs : count1325 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1325)) (countLit q [-42]) (countLit q [-44]) (count1325 q) 1 (meaningNeg42 q) (meaning1325 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1325 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1326 = true := by
  have hs : count1325 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1326)) (countLit q [-42]) (countLit q [-44]) (count1325 q) 1 1 (meaningNeg42 q) (meaningNeg44 q) (meaning1326 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 44 = true ∨ valuation q 1326 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 1325 = false ∨ valuationOf q 1327 = true := by
  have hs : count1327 q = (countLit q [-40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42, -44])
  have hm := merge_right (literal (valuationOf q) (1325)) (literal (valuationOf q) (1327)) (countLit q [-40]) (countLit q [-42, -44]) (count1327 q) 1 (meaning1325 q) (meaning1327 q) hs
  change valuationOf q 1325 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 1325 = false ∨ valuation q 1327 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42, -44])
  have hm := merge_right (literal (valuationOf q) (1326)) (literal (valuationOf q) (1328)) (countLit q [-40]) (countLit q [-42, -44]) (count1327 q) 2 (meaning1326 q) (meaning1328 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1328 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1327 = true := by
  have hs : count1327 q = (countLit q [-40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42, -44])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1327)) (countLit q [-40]) (countLit q [-42, -44]) (count1327 q) 1 (meaningNeg40 q) (meaning1327 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1327 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1325 = false ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (1325)) (literal (valuationOf q) (1328)) (countLit q [-40]) (countLit q [-42, -44]) (count1327 q) 1 1 (meaningNeg40 q) (meaning1325 q) (meaning1328 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1325 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1325 = false ∨ valuation q 1328 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1330)) (countLit q [-46]) (countLit q [-49]) (count1330 q) 1 (meaningNeg49 q) (meaning1330 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1330 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1330)) (countLit q [-46]) (countLit q [-49]) (count1330 q) 1 (meaningNeg46 q) (meaning1330 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1330 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1332 = true := by
  have hs : count1332 q = (countLit q [-51]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (1332)) (countLit q [-51]) (countLit q [-53]) (count1332 q) 1 (meaningNeg53 q) (meaning1332 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1332 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1332 = true := by
  have hs : count1332 q = (countLit q [-51]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (1332)) (countLit q [-51]) (countLit q [-53]) (count1332 q) 1 (meaningNeg51 q) (meaning1332 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1332 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 53 = true ∨ valuationOf q 1333 = true := by
  have hs : count1332 q = (countLit q [-51]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (1333)) (countLit q [-51]) (countLit q [-53]) (count1332 q) 1 1 (meaningNeg51 q) (meaningNeg53 q) (meaning1333 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 1333 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1334 = true := by
  have hs : count1334 q = (countLit q [-46, -49]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -49]) (l₂ := [-51, -53])
  have hm := merge_right (literal (valuationOf q) (1332)) (literal (valuationOf q) (1334)) (countLit q [-46, -49]) (countLit q [-51, -53]) (count1334 q) 1 (meaning1332 q) (meaning1334 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1334 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1335 = true := by
  have hs : count1334 q = (countLit q [-46, -49]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -49]) (l₂ := [-51, -53])
  have hm := merge_right (literal (valuationOf q) (1333)) (literal (valuationOf q) (1335)) (countLit q [-46, -49]) (countLit q [-51, -53]) (count1334 q) 2 (meaning1333 q) (meaning1335 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1335 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1334 = true := by
  have hs : count1334 q = (countLit q [-46, -49]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -49]) (l₂ := [-51, -53])
  have hm := merge_left (literal (valuationOf q) (1330)) (literal (valuationOf q) (1334)) (countLit q [-46, -49]) (countLit q [-51, -53]) (count1334 q) 1 (meaning1330 q) (meaning1334 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1334 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E150.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112150
