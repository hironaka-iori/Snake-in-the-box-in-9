import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 1230 = false ∨ valuationOf q 1233 = true := by
  have hs : count1232 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -35, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -35, -38])
  have hm := merge_right (literal (valuationOf q) (1230)) (literal (valuationOf q) (1233)) (countLit q [-28, -30, -32]) (countLit q [-33, -35, -38]) (count1232 q) 2 (meaning1230 q) (meaning1233 q) hs
  change valuationOf q 1230 = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 1230 = false ∨ valuation q 1233 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 1231 = false ∨ valuationOf q 1234 = true := by
  have hs : count1232 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -35, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -35, -38])
  have hm := merge_right (literal (valuationOf q) (1231)) (literal (valuationOf q) (1234)) (countLit q [-28, -30, -32]) (countLit q [-33, -35, -38]) (count1232 q) 3 (meaning1231 q) (meaning1234 q) hs
  change valuationOf q 1231 = false ∨ valuationOf q 1234 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 1231 = false ∨ valuation q 1234 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 1224 = false ∨ valuationOf q 1232 = true := by
  have hs : count1232 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -35, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -35, -38])
  have hm := merge_left (literal (valuationOf q) (1224)) (literal (valuationOf q) (1232)) (countLit q [-28, -30, -32]) (countLit q [-33, -35, -38]) (count1232 q) 1 (meaning1224 q) (meaning1232 q) hs
  change valuationOf q 1224 = false ∨ valuationOf q 1232 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 1224 = false ∨ valuation q 1232 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 1224 = false ∨ valuationOf q 1229 = false ∨ valuationOf q 1233 = true := by
  have hs : count1232 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -35, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -35, -38])
  have hm := merge_two (literal (valuationOf q) (1224)) (literal (valuationOf q) (1229)) (literal (valuationOf q) (1233)) (countLit q [-28, -30, -32]) (countLit q [-33, -35, -38]) (count1232 q) 1 1 (meaning1224 q) (meaning1229 q) (meaning1233 q) hs
  change valuationOf q 1224 = false ∨ valuationOf q 1229 = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 1224 = false ∨ valuation q 1229 = false ∨ valuation q 1233 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 1224 = false ∨ valuationOf q 1230 = false ∨ valuationOf q 1234 = true := by
  have hs : count1232 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -35, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -35, -38])
  have hm := merge_two (literal (valuationOf q) (1224)) (literal (valuationOf q) (1230)) (literal (valuationOf q) (1234)) (countLit q [-28, -30, -32]) (countLit q [-33, -35, -38]) (count1232 q) 1 2 (meaning1224 q) (meaning1230 q) (meaning1234 q) hs
  change valuationOf q 1224 = false ∨ valuationOf q 1230 = false ∨ valuationOf q 1234 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 1224 = false ∨ valuation q 1230 = false ∨ valuation q 1234 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 1224 = false ∨ valuationOf q 1231 = false ∨ valuationOf q 1235 = true := by
  have hs : count1232 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -35, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -35, -38])
  have hm := merge_two (literal (valuationOf q) (1224)) (literal (valuationOf q) (1231)) (literal (valuationOf q) (1235)) (countLit q [-28, -30, -32]) (countLit q [-33, -35, -38]) (count1232 q) 1 3 (meaning1224 q) (meaning1231 q) (meaning1235 q) hs
  change valuationOf q 1224 = false ∨ valuationOf q 1231 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 1224 = false ∨ valuation q 1231 = false ∨ valuation q 1235 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 1225 = false ∨ valuationOf q 1233 = true := by
  have hs : count1232 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -35, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -35, -38])
  have hm := merge_left (literal (valuationOf q) (1225)) (literal (valuationOf q) (1233)) (countLit q [-28, -30, -32]) (countLit q [-33, -35, -38]) (count1232 q) 2 (meaning1225 q) (meaning1233 q) hs
  change valuationOf q 1225 = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 1225 = false ∨ valuation q 1233 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 1225 = false ∨ valuationOf q 1229 = false ∨ valuationOf q 1234 = true := by
  have hs : count1232 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -35, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -35, -38])
  have hm := merge_two (literal (valuationOf q) (1225)) (literal (valuationOf q) (1229)) (literal (valuationOf q) (1234)) (countLit q [-28, -30, -32]) (countLit q [-33, -35, -38]) (count1232 q) 2 1 (meaning1225 q) (meaning1229 q) (meaning1234 q) hs
  change valuationOf q 1225 = false ∨ valuationOf q 1229 = false ∨ valuationOf q 1234 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 1225 = false ∨ valuation q 1229 = false ∨ valuation q 1234 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1238 = true := by
  have hs : count1238 q = (countLit q [-41]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1238)) (countLit q [-41]) (countLit q [-44]) (count1238 q) 1 (meaningNeg44 q) (meaning1238 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1238 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1238 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1238 = true := by
  have hs : count1238 q = (countLit q [-41]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1238)) (countLit q [-41]) (countLit q [-44]) (count1238 q) 1 (meaningNeg41 q) (meaning1238 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1238 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1238 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1239 = true := by
  have hs : count1238 q = (countLit q [-41]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1239)) (countLit q [-41]) (countLit q [-44]) (count1238 q) 1 1 (meaningNeg41 q) (meaningNeg44 q) (meaning1239 q) hs
  change (! (valuationOf q 41)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1239 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 44 = true ∨ valuation q 1239 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 1238 = false ∨ valuationOf q 1240 = true := by
  have hs : count1240 q = (countLit q [-39]) + (countLit q [-41, -44]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41, -44])
  have hm := merge_right (literal (valuationOf q) (1238)) (literal (valuationOf q) (1240)) (countLit q [-39]) (countLit q [-41, -44]) (count1240 q) 1 (meaning1238 q) (meaning1240 q) hs
  change valuationOf q 1238 = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 1238 = false ∨ valuation q 1240 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 1239 = false ∨ valuationOf q 1241 = true := by
  have hs : count1240 q = (countLit q [-39]) + (countLit q [-41, -44]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41, -44])
  have hm := merge_right (literal (valuationOf q) (1239)) (literal (valuationOf q) (1241)) (countLit q [-39]) (countLit q [-41, -44]) (count1240 q) 2 (meaning1239 q) (meaning1241 q) hs
  change valuationOf q 1239 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 1239 = false ∨ valuation q 1241 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1240 = true := by
  have hs : count1240 q = (countLit q [-39]) + (countLit q [-41, -44]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41, -44])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1240)) (countLit q [-39]) (countLit q [-41, -44]) (count1240 q) 1 (meaningNeg39 q) (meaning1240 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1240 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1238 = false ∨ valuationOf q 1241 = true := by
  have hs : count1240 q = (countLit q [-39]) + (countLit q [-41, -44]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41, -44])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (1238)) (literal (valuationOf q) (1241)) (countLit q [-39]) (countLit q [-41, -44]) (count1240 q) 1 1 (meaningNeg39 q) (meaning1238 q) (meaning1241 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1238 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1238 = false ∨ valuation q 1241 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1243 = true := by
  have hs : count1243 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1243)) (countLit q [-45]) (countLit q [-46]) (count1243 q) 1 (meaningNeg45 q) (meaning1243 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1243 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 46 = true ∨ valuationOf q 1244 = true := by
  have hs : count1243 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (1244)) (countLit q [-45]) (countLit q [-46]) (count1243 q) 1 1 (meaningNeg45 q) (meaningNeg46 q) (meaning1244 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 46 = true ∨ valuation q 1244 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1245 = true := by
  have hs : count1245 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (1245)) (countLit q [-47]) (countLit q [-50]) (count1245 q) 1 (meaningNeg50 q) (meaning1245 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1245 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1245 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1245 = true := by
  have hs : count1245 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1245)) (countLit q [-47]) (countLit q [-50]) (count1245 q) 1 (meaningNeg47 q) (meaning1245 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1245 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1245 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 50 = true ∨ valuationOf q 1246 = true := by
  have hs : count1245 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-50)) (literal (valuationOf q) (1246)) (countLit q [-47]) (countLit q [-50]) (count1245 q) 1 1 (meaningNeg47 q) (meaningNeg50 q) (meaning1246 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 50)) = false ∨ valuationOf q 1246 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 50 = true ∨ valuation q 1246 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1247 = true := by
  have hs : count1247 q = (countLit q [-45, -46]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-45, -46]) (l₂ := [-47, -50])
  have hm := merge_left (literal (valuationOf q) (1243)) (literal (valuationOf q) (1247)) (countLit q [-45, -46]) (countLit q [-47, -50]) (count1247 q) 1 (meaning1243 q) (meaning1247 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1247 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1245 = false ∨ valuationOf q 1248 = true := by
  have hs : count1247 q = (countLit q [-45, -46]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-45, -46]) (l₂ := [-47, -50])
  have hm := merge_two (literal (valuationOf q) (1243)) (literal (valuationOf q) (1245)) (literal (valuationOf q) (1248)) (countLit q [-45, -46]) (countLit q [-47, -50]) (count1247 q) 1 1 (meaning1243 q) (meaning1245 q) (meaning1248 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1245 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1245 = false ∨ valuation q 1248 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1246 = false ∨ valuationOf q 1249 = true := by
  have hs : count1247 q = (countLit q [-45, -46]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-45, -46]) (l₂ := [-47, -50])
  have hm := merge_two (literal (valuationOf q) (1243)) (literal (valuationOf q) (1246)) (literal (valuationOf q) (1249)) (countLit q [-45, -46]) (countLit q [-47, -50]) (count1247 q) 1 2 (meaning1243 q) (meaning1246 q) (meaning1249 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1246 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1246 = false ∨ valuation q 1249 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1248 = true := by
  have hs : count1247 q = (countLit q [-45, -46]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-45, -46]) (l₂ := [-47, -50])
  have hm := merge_left (literal (valuationOf q) (1244)) (literal (valuationOf q) (1248)) (countLit q [-45, -46]) (countLit q [-47, -50]) (count1247 q) 2 (meaning1244 q) (meaning1248 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1248 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1245 = false ∨ valuationOf q 1249 = true := by
  have hs : count1247 q = (countLit q [-45, -46]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-45, -46]) (l₂ := [-47, -50])
  have hm := merge_two (literal (valuationOf q) (1244)) (literal (valuationOf q) (1245)) (literal (valuationOf q) (1249)) (countLit q [-45, -46]) (countLit q [-47, -50]) (count1247 q) 2 1 (meaning1244 q) (meaning1245 q) (meaning1249 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1245 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1245 = false ∨ valuation q 1249 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1251 = true := by
  have hs : count1251 q = (countLit q [-39, -41, -44]) + (countLit q [-45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -41, -44]) (l₂ := [-45, -46, -47, -50])
  have hm := merge_right (literal (valuationOf q) (1247)) (literal (valuationOf q) (1251)) (countLit q [-39, -41, -44]) (countLit q [-45, -46, -47, -50]) (count1251 q) 1 (meaning1247 q) (meaning1251 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1251 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1252 = true := by
  have hs : count1251 q = (countLit q [-39, -41, -44]) + (countLit q [-45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -41, -44]) (l₂ := [-45, -46, -47, -50])
  have hm := merge_right (literal (valuationOf q) (1248)) (literal (valuationOf q) (1252)) (countLit q [-39, -41, -44]) (countLit q [-45, -46, -47, -50]) (count1251 q) 2 (meaning1248 q) (meaning1252 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1252 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1253 = true := by
  have hs : count1251 q = (countLit q [-39, -41, -44]) + (countLit q [-45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -41, -44]) (l₂ := [-45, -46, -47, -50])
  have hm := merge_right (literal (valuationOf q) (1249)) (literal (valuationOf q) (1253)) (countLit q [-39, -41, -44]) (countLit q [-45, -46, -47, -50]) (count1251 q) 3 (meaning1249 q) (meaning1253 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1253 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 1240 = false ∨ valuationOf q 1247 = false ∨ valuationOf q 1252 = true := by
  have hs : count1251 q = (countLit q [-39, -41, -44]) + (countLit q [-45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -41, -44]) (l₂ := [-45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1240)) (literal (valuationOf q) (1247)) (literal (valuationOf q) (1252)) (countLit q [-39, -41, -44]) (countLit q [-45, -46, -47, -50]) (count1251 q) 1 1 (meaning1240 q) (meaning1247 q) (meaning1252 q) hs
  change valuationOf q 1240 = false ∨ valuationOf q 1247 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 1240 = false ∨ valuation q 1247 = false ∨ valuation q 1252 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 1240 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1253 = true := by
  have hs : count1251 q = (countLit q [-39, -41, -44]) + (countLit q [-45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -41, -44]) (l₂ := [-45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1240)) (literal (valuationOf q) (1248)) (literal (valuationOf q) (1253)) (countLit q [-39, -41, -44]) (countLit q [-45, -46, -47, -50]) (count1251 q) 1 2 (meaning1240 q) (meaning1248 q) (meaning1253 q) hs
  change valuationOf q 1240 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 1240 = false ∨ valuation q 1248 = false ∨ valuation q 1253 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1247 = false ∨ valuationOf q 1253 = true := by
  have hs : count1251 q = (countLit q [-39, -41, -44]) + (countLit q [-45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -41, -44]) (l₂ := [-45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1241)) (literal (valuationOf q) (1247)) (literal (valuationOf q) (1253)) (countLit q [-39, -41, -44]) (countLit q [-45, -46, -47, -50]) (count1251 q) 2 1 (meaning1241 q) (meaning1247 q) (meaning1253 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1247 = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1247 = false ∨ valuation q 1253 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1254 = true := by
  have hs : count1251 q = (countLit q [-39, -41, -44]) + (countLit q [-45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -41, -44]) (l₂ := [-45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1241)) (literal (valuationOf q) (1248)) (literal (valuationOf q) (1254)) (countLit q [-39, -41, -44]) (countLit q [-45, -46, -47, -50]) (count1251 q) 2 2 (meaning1241 q) (meaning1248 q) (meaning1254 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1248 = false ∨ valuation q 1254 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E154.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112154
