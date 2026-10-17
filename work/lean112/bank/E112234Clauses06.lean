import E112234Semantics
import B112E234Inputs
namespace Snake9.Regrowth.E112234
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause193 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1238 = true := by
  have hs : count1238 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1238)) (countLit q [-34]) (countLit q [-36]) (count1238 q) 1 (meaningNeg34 q) (meaning1238 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1238 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1238 = true := counterClause193 (baseVal q)

theorem counterClause194 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 36 = true ∨ valuationOf q 1239 = true := by
  have hs : count1238 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (1239)) (countLit q [-34]) (countLit q [-36]) (count1238 q) 1 1 (meaningNeg34 q) (meaningNeg36 q) (meaning1239 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 1239 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 1239 = true := counterClause194 (baseVal q)

theorem counterClause195 (q : Nat → Bool) : valuationOf q 1238 = false ∨ valuationOf q 1240 = true := by
  have hs : count1240 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (1238)) (literal (valuationOf q) (1240)) (countLit q [-32]) (countLit q [-34, -36]) (count1240 q) 1 (meaning1238 q) (meaning1240 q) hs
  change valuationOf q 1238 = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 1238 = false ∨ valuation q 1240 = true := counterClause195 (baseVal q)

theorem counterClause196 (q : Nat → Bool) : valuationOf q 1239 = false ∨ valuationOf q 1241 = true := by
  have hs : count1240 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (1239)) (literal (valuationOf q) (1241)) (countLit q [-32]) (countLit q [-34, -36]) (count1240 q) 2 (meaning1239 q) (meaning1241 q) hs
  change valuationOf q 1239 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 1239 = false ∨ valuation q 1241 = true := counterClause196 (baseVal q)

theorem counterClause197 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1240 = true := by
  have hs : count1240 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1240)) (countLit q [-32]) (countLit q [-34, -36]) (count1240 q) 1 (meaningNeg32 q) (meaning1240 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1240 = true := counterClause197 (baseVal q)

theorem counterClause198 (q : Nat → Bool) : valuationOf q 1240 = false ∨ valuationOf q 1243 = true := by
  have hs : count1243 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -34, -36])
  have hm := merge_right (literal (valuationOf q) (1240)) (literal (valuationOf q) (1243)) (countLit q [-27, -29, -30]) (countLit q [-32, -34, -36]) (count1243 q) 1 (meaning1240 q) (meaning1243 q) hs
  change valuationOf q 1240 = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 1240 = false ∨ valuation q 1243 = true := counterClause198 (baseVal q)

theorem counterClause199 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1244 = true := by
  have hs : count1243 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -34, -36])
  have hm := merge_right (literal (valuationOf q) (1241)) (literal (valuationOf q) (1244)) (countLit q [-27, -29, -30]) (countLit q [-32, -34, -36]) (count1243 q) 2 (meaning1241 q) (meaning1244 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1244 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 1235 = false ∨ valuationOf q 1243 = true := by
  have hs : count1243 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -34, -36])
  have hm := merge_left (literal (valuationOf q) (1235)) (literal (valuationOf q) (1243)) (countLit q [-27, -29, -30]) (countLit q [-32, -34, -36]) (count1243 q) 1 (meaning1235 q) (meaning1243 q) hs
  change valuationOf q 1235 = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 1235 = false ∨ valuation q 1243 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 1235 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1244 = true := by
  have hs : count1243 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -34, -36])
  have hm := merge_two (literal (valuationOf q) (1235)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1244)) (countLit q [-27, -29, -30]) (countLit q [-32, -34, -36]) (count1243 q) 1 1 (meaning1235 q) (meaning1240 q) (meaning1244 q) hs
  change valuationOf q 1235 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 1235 = false ∨ valuation q 1240 = false ∨ valuation q 1244 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 1236 = false ∨ valuationOf q 1244 = true := by
  have hs : count1243 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -34, -36])
  have hm := merge_left (literal (valuationOf q) (1236)) (literal (valuationOf q) (1244)) (countLit q [-27, -29, -30]) (countLit q [-32, -34, -36]) (count1243 q) 2 (meaning1236 q) (meaning1244 q) hs
  change valuationOf q 1236 = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 1236 = false ∨ valuation q 1244 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 1236 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1245 = true := by
  have hs : count1243 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -34, -36])
  have hm := merge_two (literal (valuationOf q) (1236)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1245)) (countLit q [-27, -29, -30]) (countLit q [-32, -34, -36]) (count1243 q) 2 1 (meaning1236 q) (meaning1240 q) (meaning1245 q) hs
  change valuationOf q 1236 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 1236 = false ∨ valuation q 1240 = false ∨ valuation q 1245 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1249 = true := by
  have hs : count1249 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1249)) (countLit q [-39]) (countLit q [-42]) (count1249 q) 1 (meaningNeg42 q) (meaning1249 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1249 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1249 = true := by
  have hs : count1249 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1249)) (countLit q [-39]) (countLit q [-42]) (count1249 q) 1 (meaningNeg39 q) (meaning1249 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1249 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1251 = true := by
  have hs : count1251 q = (countLit q [-37]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39, -42])
  have hm := merge_right (literal (valuationOf q) (1249)) (literal (valuationOf q) (1251)) (countLit q [-37]) (countLit q [-39, -42]) (count1251 q) 1 (meaning1249 q) (meaning1251 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1251 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1251 = true := by
  have hs : count1251 q = (countLit q [-37]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39, -42])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1251)) (countLit q [-37]) (countLit q [-39, -42]) (count1251 q) 1 (meaningNeg37 q) (meaning1251 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1251 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1249 = false ∨ valuationOf q 1252 = true := by
  have hs : count1251 q = (countLit q [-37]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39, -42])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (1249)) (literal (valuationOf q) (1252)) (countLit q [-37]) (countLit q [-39, -42]) (count1251 q) 1 1 (meaningNeg37 q) (meaning1249 q) (meaning1252 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1249 = false ∨ valuation q 1252 = true := counterClause208 (baseVal q)

theorem counterClause209 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1254 = true := by
  have hs : count1254 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1254)) (countLit q [-44]) (countLit q [-45]) (count1254 q) 1 (meaningNeg44 q) (meaning1254 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1254 = true := counterClause209 (baseVal q)

theorem counterClause210 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1256 = true := by
  have hs : count1256 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (1256)) (countLit q [-47]) (countLit q [-50]) (count1256 q) 1 (meaningNeg50 q) (meaning1256 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1256 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1256 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1256 = true := by
  have hs : count1256 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1256)) (countLit q [-47]) (countLit q [-50]) (count1256 q) 1 (meaningNeg47 q) (meaning1256 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1256 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1256 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 1256 = false ∨ valuationOf q 1258 = true := by
  have hs : count1258 q = (countLit q [-44, -45]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-47, -50])
  have hm := merge_right (literal (valuationOf q) (1256)) (literal (valuationOf q) (1258)) (countLit q [-44, -45]) (countLit q [-47, -50]) (count1258 q) 1 (meaning1256 q) (meaning1258 q) hs
  change valuationOf q 1256 = false ∨ valuationOf q 1258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 1256 = false ∨ valuation q 1258 = true := counterClause212 (baseVal q)

theorem counterClause213 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1258 = true := by
  have hs : count1258 q = (countLit q [-44, -45]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-47, -50])
  have hm := merge_left (literal (valuationOf q) (1254)) (literal (valuationOf q) (1258)) (countLit q [-44, -45]) (countLit q [-47, -50]) (count1258 q) 1 (meaning1254 q) (meaning1258 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1258 = true := counterClause213 (baseVal q)

theorem counterClause214 (q : Nat → Bool) : valuationOf q 1258 = false ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-37, -39, -42]) + (countLit q [-44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -42]) (l₂ := [-44, -45, -47, -50])
  have hm := merge_right (literal (valuationOf q) (1258)) (literal (valuationOf q) (1262)) (countLit q [-37, -39, -42]) (countLit q [-44, -45, -47, -50]) (count1262 q) 1 (meaning1258 q) (meaning1262 q) hs
  change valuationOf q 1258 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 1258 = false ∨ valuation q 1262 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1263 = true := by
  have hs : count1262 q = (countLit q [-37, -39, -42]) + (countLit q [-44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -42]) (l₂ := [-44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1258)) (literal (valuationOf q) (1263)) (countLit q [-37, -39, -42]) (countLit q [-44, -45, -47, -50]) (count1262 q) 1 1 (meaning1251 q) (meaning1258 q) (meaning1263 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1258 = false ∨ valuation q 1263 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1264 = true := by
  have hs : count1262 q = (countLit q [-37, -39, -42]) + (countLit q [-44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -42]) (l₂ := [-44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1252)) (literal (valuationOf q) (1258)) (literal (valuationOf q) (1264)) (countLit q [-37, -39, -42]) (countLit q [-44, -45, -47, -50]) (count1262 q) 2 1 (meaning1252 q) (meaning1258 q) (meaning1264 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1258 = false ∨ valuation q 1264 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1269 = true := by
  have hs : count1269 q = (countLit q [-27, -29, -30, -32, -34, -36]) + (countLit q [-37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -34, -36]) (l₂ := [-37, -39, -42, -44, -45, -47, -50])
  have hm := merge_right (literal (valuationOf q) (1262)) (literal (valuationOf q) (1269)) (countLit q [-27, -29, -30, -32, -34, -36]) (countLit q [-37, -39, -42, -44, -45, -47, -50]) (count1269 q) 1 (meaning1262 q) (meaning1269 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1269 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1262 = false ∨ valuationOf q 1270 = true := by
  have hs : count1269 q = (countLit q [-27, -29, -30, -32, -34, -36]) + (countLit q [-37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -34, -36]) (l₂ := [-37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1243)) (literal (valuationOf q) (1262)) (literal (valuationOf q) (1270)) (countLit q [-27, -29, -30, -32, -34, -36]) (countLit q [-37, -39, -42, -44, -45, -47, -50]) (count1269 q) 1 1 (meaning1243 q) (meaning1262 q) (meaning1270 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1262 = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1262 = false ∨ valuation q 1270 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1263 = false ∨ valuationOf q 1271 = true := by
  have hs : count1269 q = (countLit q [-27, -29, -30, -32, -34, -36]) + (countLit q [-37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -34, -36]) (l₂ := [-37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1243)) (literal (valuationOf q) (1263)) (literal (valuationOf q) (1271)) (countLit q [-27, -29, -30, -32, -34, -36]) (countLit q [-37, -39, -42, -44, -45, -47, -50]) (count1269 q) 1 2 (meaning1243 q) (meaning1263 q) (meaning1271 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1263 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1263 = false ∨ valuation q 1271 = true := counterClause219 (baseVal q)

theorem counterClause220 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1272 = true := by
  have hs : count1269 q = (countLit q [-27, -29, -30, -32, -34, -36]) + (countLit q [-37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -34, -36]) (l₂ := [-37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1243)) (literal (valuationOf q) (1264)) (literal (valuationOf q) (1272)) (countLit q [-27, -29, -30, -32, -34, -36]) (countLit q [-37, -39, -42, -44, -45, -47, -50]) (count1269 q) 1 3 (meaning1243 q) (meaning1264 q) (meaning1272 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1264 = false ∨ valuation q 1272 = true := counterClause220 (baseVal q)

theorem counterClause221 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1262 = false ∨ valuationOf q 1271 = true := by
  have hs : count1269 q = (countLit q [-27, -29, -30, -32, -34, -36]) + (countLit q [-37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -34, -36]) (l₂ := [-37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1244)) (literal (valuationOf q) (1262)) (literal (valuationOf q) (1271)) (countLit q [-27, -29, -30, -32, -34, -36]) (countLit q [-37, -39, -42, -44, -45, -47, -50]) (count1269 q) 2 1 (meaning1244 q) (meaning1262 q) (meaning1271 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1262 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1262 = false ∨ valuation q 1271 = true := counterClause221 (baseVal q)

theorem counterClause222 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1263 = false ∨ valuationOf q 1272 = true := by
  have hs : count1269 q = (countLit q [-27, -29, -30, -32, -34, -36]) + (countLit q [-37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -34, -36]) (l₂ := [-37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1244)) (literal (valuationOf q) (1263)) (literal (valuationOf q) (1272)) (countLit q [-27, -29, -30, -32, -34, -36]) (countLit q [-37, -39, -42, -44, -45, -47, -50]) (count1269 q) 2 2 (meaning1244 q) (meaning1263 q) (meaning1272 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1263 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1263 = false ∨ valuation q 1272 = true := counterClause222 (baseVal q)

theorem counterClause223 (q : Nat → Bool) : valuationOf q 1245 = false ∨ valuationOf q 1262 = false ∨ valuationOf q 1272 = true := by
  have hs : count1269 q = (countLit q [-27, -29, -30, -32, -34, -36]) + (countLit q [-37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -34, -36]) (l₂ := [-37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1245)) (literal (valuationOf q) (1262)) (literal (valuationOf q) (1272)) (countLit q [-27, -29, -30, -32, -34, -36]) (countLit q [-37, -39, -42, -44, -45, -47, -50]) (count1269 q) 3 1 (meaning1245 q) (meaning1262 q) (meaning1272 q) hs
  change valuationOf q 1245 = false ∨ valuationOf q 1262 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 1245 = false ∨ valuation q 1262 = false ∨ valuation q 1272 = true := counterClause223 (baseVal q)

theorem counterClause224 (q : Nat → Bool) : valuationOf q 1223 = false ∨ valuationOf q 1272 = false ∨ valuationOf q 1285 = true := by
  have hs : count1280 q = (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) + (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (l₂ := [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1223)) (literal (valuationOf q) (1272)) (literal (valuationOf q) (1285)) (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]) (countLit q [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (count1280 q) 2 4 (meaning1223 q) (meaning1272 q) (meaning1285 q) hs
  change valuationOf q 1223 = false ∨ valuationOf q 1272 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 1223 = false ∨ valuation q 1272 = false ∨ valuation q 1285 = true := counterClause224 (baseVal q)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E234.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112234
