import E112182Semantics
import B112E182Inputs
namespace Snake9.Regrowth.E112182
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause129 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1272 = true := by
  have hs : count1271 q = (countLit q [-28, -29, -36]) + (countLit q [-37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36]) (l₂ := [-37, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1269)) (literal (valuationOf q) (1272)) (countLit q [-28, -29, -36]) (countLit q [-37, -38, -40]) (count1271 q) 2 (meaning1269 q) (meaning1272 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1272 = true := counterClause129 (baseVal q)

theorem counterClause130 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1271 = true := by
  have hs : count1271 q = (countLit q [-28, -29, -36]) + (countLit q [-37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36]) (l₂ := [-37, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1263)) (literal (valuationOf q) (1271)) (countLit q [-28, -29, -36]) (countLit q [-37, -38, -40]) (count1271 q) 1 (meaning1263 q) (meaning1271 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1271 = true := counterClause130 (baseVal q)

theorem counterClause131 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1272 = true := by
  have hs : count1271 q = (countLit q [-28, -29, -36]) + (countLit q [-37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36]) (l₂ := [-37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1272)) (countLit q [-28, -29, -36]) (countLit q [-37, -38, -40]) (count1271 q) 1 1 (meaning1263 q) (meaning1268 q) (meaning1272 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1268 = false ∨ valuation q 1272 = true := counterClause131 (baseVal q)

theorem counterClause132 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1269 = false ∨ valuationOf q 1273 = true := by
  have hs : count1271 q = (countLit q [-28, -29, -36]) + (countLit q [-37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36]) (l₂ := [-37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1269)) (literal (valuationOf q) (1273)) (countLit q [-28, -29, -36]) (countLit q [-37, -38, -40]) (count1271 q) 1 2 (meaning1263 q) (meaning1269 q) (meaning1273 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1269 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1269 = false ∨ valuation q 1273 = true := counterClause132 (baseVal q)

theorem counterClause133 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1272 = true := by
  have hs : count1271 q = (countLit q [-28, -29, -36]) + (countLit q [-37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36]) (l₂ := [-37, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1264)) (literal (valuationOf q) (1272)) (countLit q [-28, -29, -36]) (countLit q [-37, -38, -40]) (count1271 q) 2 (meaning1264 q) (meaning1272 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1272 = true := counterClause133 (baseVal q)

theorem counterClause134 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1273 = true := by
  have hs : count1271 q = (countLit q [-28, -29, -36]) + (countLit q [-37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36]) (l₂ := [-37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1264)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1273)) (countLit q [-28, -29, -36]) (countLit q [-37, -38, -40]) (count1271 q) 2 1 (meaning1264 q) (meaning1268 q) (meaning1273 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1268 = false ∨ valuation q 1273 = true := counterClause134 (baseVal q)

theorem counterClause135 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-45]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1277)) (countLit q [-45]) (countLit q [-48]) (count1277 q) 1 (meaningNeg48 q) (meaning1277 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1277 = true := counterClause135 (baseVal q)

theorem counterClause136 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-45]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1277)) (countLit q [-45]) (countLit q [-48]) (count1277 q) 1 (meaningNeg45 q) (meaning1277 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1277 = true := counterClause136 (baseVal q)

theorem counterClause137 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 48 = true ∨ valuationOf q 1278 = true := by
  have hs : count1277 q = (countLit q [-45]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (1278)) (countLit q [-45]) (countLit q [-48]) (count1277 q) 1 1 (meaningNeg45 q) (meaningNeg48 q) (meaning1278 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 1278 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 48 = true ∨ valuation q 1278 = true := counterClause137 (baseVal q)

theorem counterClause138 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1279 = true := by
  have hs : count1279 q = (countLit q [-42]) + (countLit q [-45, -48]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45, -48])
  have hm := merge_right (literal (valuationOf q) (1277)) (literal (valuationOf q) (1279)) (countLit q [-42]) (countLit q [-45, -48]) (count1279 q) 1 (meaning1277 q) (meaning1279 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1279 = true := counterClause138 (baseVal q)

theorem counterClause139 (q : Nat → Bool) : valuationOf q 1278 = false ∨ valuationOf q 1280 = true := by
  have hs : count1279 q = (countLit q [-42]) + (countLit q [-45, -48]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45, -48])
  have hm := merge_right (literal (valuationOf q) (1278)) (literal (valuationOf q) (1280)) (countLit q [-42]) (countLit q [-45, -48]) (count1279 q) 2 (meaning1278 q) (meaning1280 q) hs
  change valuationOf q 1278 = false ∨ valuationOf q 1280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 1278 = false ∨ valuation q 1280 = true := counterClause139 (baseVal q)

theorem counterClause140 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1282 = true := by
  have hs : count1282 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (1282)) (countLit q [-52]) (countLit q [-53]) (count1282 q) 1 (meaningNeg53 q) (meaning1282 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1282 = true := counterClause140 (baseVal q)

theorem counterClause141 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1282 = true := by
  have hs : count1282 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1282)) (countLit q [-52]) (countLit q [-53]) (count1282 q) 1 (meaningNeg52 q) (meaning1282 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1282 = true := counterClause141 (baseVal q)

theorem counterClause142 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 53 = true ∨ valuationOf q 1283 = true := by
  have hs : count1282 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (1283)) (countLit q [-52]) (countLit q [-53]) (count1282 q) 1 1 (meaningNeg52 q) (meaningNeg53 q) (meaning1283 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 1283 = true := counterClause142 (baseVal q)

theorem counterClause143 (q : Nat → Bool) : valuationOf q 1282 = false ∨ valuationOf q 1284 = true := by
  have hs : count1284 q = (countLit q [-50]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52, -53])
  have hm := merge_right (literal (valuationOf q) (1282)) (literal (valuationOf q) (1284)) (countLit q [-50]) (countLit q [-52, -53]) (count1284 q) 1 (meaning1282 q) (meaning1284 q) hs
  change valuationOf q 1282 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 1282 = false ∨ valuation q 1284 = true := counterClause143 (baseVal q)

theorem counterClause144 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1285 = true := by
  have hs : count1284 q = (countLit q [-50]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52, -53])
  have hm := merge_right (literal (valuationOf q) (1283)) (literal (valuationOf q) (1285)) (countLit q [-50]) (countLit q [-52, -53]) (count1284 q) 2 (meaning1283 q) (meaning1285 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1285 = true := counterClause144 (baseVal q)

theorem counterClause145 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1284 = true := by
  have hs : count1284 q = (countLit q [-50]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52, -53])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1284)) (countLit q [-50]) (countLit q [-52, -53]) (count1284 q) 1 (meaningNeg50 q) (meaning1284 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1284 = true := counterClause145 (baseVal q)

theorem counterClause146 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1282 = false ∨ valuationOf q 1285 = true := by
  have hs : count1284 q = (countLit q [-50]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52, -53])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1285)) (countLit q [-50]) (countLit q [-52, -53]) (count1284 q) 1 1 (meaningNeg50 q) (meaning1282 q) (meaning1285 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1282 = false ∨ valuation q 1285 = true := counterClause146 (baseVal q)

theorem counterClause147 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1283 = false ∨ valuationOf q 1286 = true := by
  have hs : count1284 q = (countLit q [-50]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52, -53])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (1283)) (literal (valuationOf q) (1286)) (countLit q [-50]) (countLit q [-52, -53]) (count1284 q) 1 2 (meaningNeg50 q) (meaning1283 q) (meaning1286 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1283 = false ∨ valuation q 1286 = true := counterClause147 (baseVal q)

theorem counterClause148 (q : Nat → Bool) : valuationOf q 1284 = false ∨ valuationOf q 1287 = true := by
  have hs : count1287 q = (countLit q [-42, -45, -48]) + (countLit q [-50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -48]) (l₂ := [-50, -52, -53])
  have hm := merge_right (literal (valuationOf q) (1284)) (literal (valuationOf q) (1287)) (countLit q [-42, -45, -48]) (countLit q [-50, -52, -53]) (count1287 q) 1 (meaning1284 q) (meaning1287 q) hs
  change valuationOf q 1284 = false ∨ valuationOf q 1287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 1284 = false ∨ valuation q 1287 = true := counterClause148 (baseVal q)

theorem counterClause149 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1288 = true := by
  have hs : count1287 q = (countLit q [-42, -45, -48]) + (countLit q [-50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -48]) (l₂ := [-50, -52, -53])
  have hm := merge_right (literal (valuationOf q) (1285)) (literal (valuationOf q) (1288)) (countLit q [-42, -45, -48]) (countLit q [-50, -52, -53]) (count1287 q) 2 (meaning1285 q) (meaning1288 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1288 = true := counterClause149 (baseVal q)

theorem counterClause150 (q : Nat → Bool) : valuationOf q 1286 = false ∨ valuationOf q 1289 = true := by
  have hs : count1287 q = (countLit q [-42, -45, -48]) + (countLit q [-50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -48]) (l₂ := [-50, -52, -53])
  have hm := merge_right (literal (valuationOf q) (1286)) (literal (valuationOf q) (1289)) (countLit q [-42, -45, -48]) (countLit q [-50, -52, -53]) (count1287 q) 3 (meaning1286 q) (meaning1289 q) hs
  change valuationOf q 1286 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 1286 = false ∨ valuation q 1289 = true := counterClause150 (baseVal q)

theorem counterClause151 (q : Nat → Bool) : valuationOf q 1279 = false ∨ valuationOf q 1287 = true := by
  have hs : count1287 q = (countLit q [-42, -45, -48]) + (countLit q [-50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -48]) (l₂ := [-50, -52, -53])
  have hm := merge_left (literal (valuationOf q) (1279)) (literal (valuationOf q) (1287)) (countLit q [-42, -45, -48]) (countLit q [-50, -52, -53]) (count1287 q) 1 (meaning1279 q) (meaning1287 q) hs
  change valuationOf q 1279 = false ∨ valuationOf q 1287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 1279 = false ∨ valuation q 1287 = true := counterClause151 (baseVal q)

theorem counterClause152 (q : Nat → Bool) : valuationOf q 1279 = false ∨ valuationOf q 1284 = false ∨ valuationOf q 1288 = true := by
  have hs : count1287 q = (countLit q [-42, -45, -48]) + (countLit q [-50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -48]) (l₂ := [-50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1279)) (literal (valuationOf q) (1284)) (literal (valuationOf q) (1288)) (countLit q [-42, -45, -48]) (countLit q [-50, -52, -53]) (count1287 q) 1 1 (meaning1279 q) (meaning1284 q) (meaning1288 q) hs
  change valuationOf q 1279 = false ∨ valuationOf q 1284 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 1279 = false ∨ valuation q 1284 = false ∨ valuation q 1288 = true := counterClause152 (baseVal q)

theorem counterClause153 (q : Nat → Bool) : valuationOf q 1279 = false ∨ valuationOf q 1285 = false ∨ valuationOf q 1289 = true := by
  have hs : count1287 q = (countLit q [-42, -45, -48]) + (countLit q [-50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -48]) (l₂ := [-50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1279)) (literal (valuationOf q) (1285)) (literal (valuationOf q) (1289)) (countLit q [-42, -45, -48]) (countLit q [-50, -52, -53]) (count1287 q) 1 2 (meaning1279 q) (meaning1285 q) (meaning1289 q) hs
  change valuationOf q 1279 = false ∨ valuationOf q 1285 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 1279 = false ∨ valuation q 1285 = false ∨ valuation q 1289 = true := counterClause153 (baseVal q)

theorem counterClause154 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1288 = true := by
  have hs : count1287 q = (countLit q [-42, -45, -48]) + (countLit q [-50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -48]) (l₂ := [-50, -52, -53])
  have hm := merge_left (literal (valuationOf q) (1280)) (literal (valuationOf q) (1288)) (countLit q [-42, -45, -48]) (countLit q [-50, -52, -53]) (count1287 q) 2 (meaning1280 q) (meaning1288 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1288 = true := counterClause154 (baseVal q)

theorem counterClause155 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1284 = false ∨ valuationOf q 1289 = true := by
  have hs : count1287 q = (countLit q [-42, -45, -48]) + (countLit q [-50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -48]) (l₂ := [-50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1280)) (literal (valuationOf q) (1284)) (literal (valuationOf q) (1289)) (countLit q [-42, -45, -48]) (countLit q [-50, -52, -53]) (count1287 q) 2 1 (meaning1280 q) (meaning1284 q) (meaning1289 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1284 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1284 = false ∨ valuation q 1289 = true := counterClause155 (baseVal q)

theorem counterClause156 (q : Nat → Bool) : valuationOf q 1287 = false ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-28, -29, -36, -37, -38, -40]) + (countLit q [-42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36, -37, -38, -40]) (l₂ := [-42, -45, -48, -50, -52, -53])
  have hm := merge_right (literal (valuationOf q) (1287)) (literal (valuationOf q) (1293)) (countLit q [-28, -29, -36, -37, -38, -40]) (countLit q [-42, -45, -48, -50, -52, -53]) (count1293 q) 1 (meaning1287 q) (meaning1293 q) hs
  change valuationOf q 1287 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 1287 = false ∨ valuation q 1293 = true := counterClause156 (baseVal q)

theorem counterClause157 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-28, -29, -36, -37, -38, -40]) + (countLit q [-42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36, -37, -38, -40]) (l₂ := [-42, -45, -48, -50, -52, -53])
  have hm := merge_right (literal (valuationOf q) (1288)) (literal (valuationOf q) (1294)) (countLit q [-28, -29, -36, -37, -38, -40]) (countLit q [-42, -45, -48, -50, -52, -53]) (count1293 q) 2 (meaning1288 q) (meaning1294 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1294 = true := counterClause157 (baseVal q)

theorem counterClause158 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1295 = true := by
  have hs : count1293 q = (countLit q [-28, -29, -36, -37, -38, -40]) + (countLit q [-42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36, -37, -38, -40]) (l₂ := [-42, -45, -48, -50, -52, -53])
  have hm := merge_right (literal (valuationOf q) (1289)) (literal (valuationOf q) (1295)) (countLit q [-28, -29, -36, -37, -38, -40]) (countLit q [-42, -45, -48, -50, -52, -53]) (count1293 q) 3 (meaning1289 q) (meaning1295 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1295 = true := counterClause158 (baseVal q)

theorem counterClause159 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-28, -29, -36, -37, -38, -40]) + (countLit q [-42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36, -37, -38, -40]) (l₂ := [-42, -45, -48, -50, -52, -53])
  have hm := merge_left (literal (valuationOf q) (1271)) (literal (valuationOf q) (1293)) (countLit q [-28, -29, -36, -37, -38, -40]) (countLit q [-42, -45, -48, -50, -52, -53]) (count1293 q) 1 (meaning1271 q) (meaning1293 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1293 = true := counterClause159 (baseVal q)

theorem counterClause160 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1287 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-28, -29, -36, -37, -38, -40]) + (countLit q [-42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36, -37, -38, -40]) (l₂ := [-42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1287)) (literal (valuationOf q) (1294)) (countLit q [-28, -29, -36, -37, -38, -40]) (countLit q [-42, -45, -48, -50, -52, -53]) (count1293 q) 1 1 (meaning1271 q) (meaning1287 q) (meaning1294 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1287 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1287 = false ∨ valuation q 1294 = true := counterClause160 (baseVal q)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E182.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112182
