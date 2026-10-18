import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 214 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_left (literal (valuationOf q) (214)) (literal (valuationOf q) (419)) (countLit q [214]) (countLit q [215]) (count419 q) 1 (meaning214 q) (meaning419 q) hs
  change valuationOf q 214 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 419 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [212, 213]) + (countLit q [214, 215]) := List.countP_append (p := literal q) (l₁ := [212, 213]) (l₂ := [214, 215])
  have hm := merge_right (literal (valuationOf q) (419)) (literal (valuationOf q) (421)) (countLit q [212, 213]) (countLit q [214, 215]) (count421 q) 1 (meaning419 q) (meaning421 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 421 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [212, 213]) + (countLit q [214, 215]) := List.countP_append (p := literal q) (l₁ := [212, 213]) (l₂ := [214, 215])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (421)) (countLit q [212, 213]) (countLit q [214, 215]) (count421 q) 1 (meaning417 q) (meaning421 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 421 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [208, 209, 210, 211]) + (countLit q [212, 213, 214, 215]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211]) (l₂ := [212, 213, 214, 215])
  have hm := merge_right (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (countLit q [208, 209, 210, 211]) (countLit q [212, 213, 214, 215]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [208, 209, 210, 211]) + (countLit q [212, 213, 214, 215]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211]) (l₂ := [212, 213, 214, 215])
  have hm := merge_left (literal (valuationOf q) (415)) (literal (valuationOf q) (423)) (countLit q [208, 209, 210, 211]) (countLit q [212, 213, 214, 215]) (count423 q) 1 (meaning415 q) (meaning423 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 423 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 421 = false ∨ valuationOf q 424 = true := by
  have hs : count423 q = (countLit q [208, 209, 210, 211]) + (countLit q [212, 213, 214, 215]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211]) (l₂ := [212, 213, 214, 215])
  have hm := merge_two (literal (valuationOf q) (415)) (literal (valuationOf q) (421)) (literal (valuationOf q) (424)) (countLit q [208, 209, 210, 211]) (countLit q [212, 213, 214, 215]) (count423 q) 1 1 (meaning415 q) (meaning421 q) (meaning424 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 421 = false ∨ valuationOf q 424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 421 = false ∨ valuation q 424 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 416 = false ∨ valuationOf q 424 = true := by
  have hs : count423 q = (countLit q [208, 209, 210, 211]) + (countLit q [212, 213, 214, 215]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211]) (l₂ := [212, 213, 214, 215])
  have hm := merge_left (literal (valuationOf q) (416)) (literal (valuationOf q) (424)) (countLit q [208, 209, 210, 211]) (countLit q [212, 213, 214, 215]) (count423 q) 2 (meaning416 q) (meaning424 q) hs
  change valuationOf q 416 = false ∨ valuationOf q 424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 416 = false ∨ valuation q 424 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [216]) + (countLit q [217]) := List.countP_append (p := literal q) (l₁ := [216]) (l₂ := [217])
  have hm := merge_right (literal (valuationOf q) (217)) (literal (valuationOf q) (425)) (countLit q [216]) (countLit q [217]) (count425 q) 1 (meaning217 q) (meaning425 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 425 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [216, 217]) + (countLit q [218, 219]) := List.countP_append (p := literal q) (l₁ := [216, 217]) (l₂ := [218, 219])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (429)) (countLit q [216, 217]) (countLit q [218, 219]) (count429 q) 1 (meaning425 q) (meaning429 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 429 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [220]) + (countLit q [221]) := List.countP_append (p := literal q) (l₁ := [220]) (l₂ := [221])
  have hm := merge_right (literal (valuationOf q) (221)) (literal (valuationOf q) (431)) (countLit q [220]) (countLit q [221]) (count431 q) 1 (meaning221 q) (meaning431 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 431 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [222]) + (countLit q [223]) := List.countP_append (p := literal q) (l₁ := [222]) (l₂ := [223])
  have hm := merge_left (literal (valuationOf q) (222)) (literal (valuationOf q) (433)) (countLit q [222]) (countLit q [223]) (count433 q) 1 (meaning222 q) (meaning433 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 433 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [220, 221]) + (countLit q [222, 223]) := List.countP_append (p := literal q) (l₁ := [220, 221]) (l₂ := [222, 223])
  have hm := merge_right (literal (valuationOf q) (433)) (literal (valuationOf q) (435)) (countLit q [220, 221]) (countLit q [222, 223]) (count435 q) 1 (meaning433 q) (meaning435 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 435 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [220, 221]) + (countLit q [222, 223]) := List.countP_append (p := literal q) (l₁ := [220, 221]) (l₂ := [222, 223])
  have hm := merge_left (literal (valuationOf q) (431)) (literal (valuationOf q) (435)) (countLit q [220, 221]) (countLit q [222, 223]) (count435 q) 1 (meaning431 q) (meaning435 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 435 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [220, 221]) + (countLit q [222, 223]) := List.countP_append (p := literal q) (l₁ := [220, 221]) (l₂ := [222, 223])
  have hm := merge_two (literal (valuationOf q) (431)) (literal (valuationOf q) (433)) (literal (valuationOf q) (436)) (countLit q [220, 221]) (countLit q [222, 223]) (count435 q) 1 1 (meaning431 q) (meaning433 q) (meaning436 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 433 = false ∨ valuation q 436 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [216, 217, 218, 219]) + (countLit q [220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [216, 217, 218, 219]) (l₂ := [220, 221, 222, 223])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [216, 217, 218, 219]) (countLit q [220, 221, 222, 223]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 436 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [216, 217, 218, 219]) + (countLit q [220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [216, 217, 218, 219]) (l₂ := [220, 221, 222, 223])
  have hm := merge_right (literal (valuationOf q) (436)) (literal (valuationOf q) (438)) (countLit q [216, 217, 218, 219]) (countLit q [220, 221, 222, 223]) (count437 q) 2 (meaning436 q) (meaning438 q) hs
  change valuationOf q 436 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 436 = false ∨ valuation q 438 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [216, 217, 218, 219]) + (countLit q [220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [216, 217, 218, 219]) (l₂ := [220, 221, 222, 223])
  have hm := merge_left (literal (valuationOf q) (429)) (literal (valuationOf q) (437)) (countLit q [216, 217, 218, 219]) (countLit q [220, 221, 222, 223]) (count437 q) 1 (meaning429 q) (meaning437 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 437 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [208, 209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222, 223])
  have hm := merge_right (literal (valuationOf q) (437)) (literal (valuationOf q) (439)) (countLit q [208, 209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) (count439 q) 1 (meaning437 q) (meaning439 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 439 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 438 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [208, 209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222, 223])
  have hm := merge_right (literal (valuationOf q) (438)) (literal (valuationOf q) (440)) (countLit q [208, 209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) (count439 q) 2 (meaning438 q) (meaning440 q) hs
  change valuationOf q 438 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 438 = false ∨ valuation q 440 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [208, 209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222, 223])
  have hm := merge_left (literal (valuationOf q) (423)) (literal (valuationOf q) (439)) (countLit q [208, 209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) (count439 q) 1 (meaning423 q) (meaning439 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 439 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 437 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [208, 209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222, 223])
  have hm := merge_two (literal (valuationOf q) (423)) (literal (valuationOf q) (437)) (literal (valuationOf q) (440)) (countLit q [208, 209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) (count439 q) 1 1 (meaning423 q) (meaning437 q) (meaning440 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 437 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 437 = false ∨ valuation q 440 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 424 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [208, 209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222, 223])
  have hm := merge_left (literal (valuationOf q) (424)) (literal (valuationOf q) (440)) (countLit q [208, 209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) (count439 q) 2 (meaning424 q) (meaning440 q) hs
  change valuationOf q 424 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 424 = false ∨ valuation q 440 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) + (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (l₂ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223])
  have hm := merge_right (literal (valuationOf q) (439)) (literal (valuationOf q) (441)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (count441 q) 1 (meaning439 q) (meaning441 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 441 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 440 = false ∨ valuationOf q 442 = true := by
  have hs : count441 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) + (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (l₂ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223])
  have hm := merge_right (literal (valuationOf q) (440)) (literal (valuationOf q) (442)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (count441 q) 2 (meaning440 q) (meaning442 q) hs
  change valuationOf q 440 = false ∨ valuationOf q 442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 440 = false ∨ valuation q 442 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) + (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (l₂ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223])
  have hm := merge_left (literal (valuationOf q) (409)) (literal (valuationOf q) (441)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (count441 q) 1 (meaning409 q) (meaning441 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 441 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 439 = false ∨ valuationOf q 442 = true := by
  have hs : count441 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) + (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (l₂ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223])
  have hm := merge_two (literal (valuationOf q) (409)) (literal (valuationOf q) (439)) (literal (valuationOf q) (442)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (count441 q) 1 1 (meaning409 q) (meaning439 q) (meaning442 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 439 = false ∨ valuationOf q 442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 439 = false ∨ valuation q 442 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 442 = true := by
  have hs : count441 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) + (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (l₂ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223])
  have hm := merge_left (literal (valuationOf q) (410)) (literal (valuationOf q) (442)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (count441 q) 2 (meaning410 q) (meaning442 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 442 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [226]) + (countLit q [227]) := List.countP_append (p := literal q) (l₁ := [226]) (l₂ := [227])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (445)) (countLit q [226]) (countLit q [227]) (count445 q) 1 (meaning227 q) (meaning445 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 445 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [226]) + (countLit q [227]) := List.countP_append (p := literal q) (l₁ := [226]) (l₂ := [227])
  have hm := merge_left (literal (valuationOf q) (226)) (literal (valuationOf q) (445)) (countLit q [226]) (countLit q [227]) (count445 q) 1 (meaning226 q) (meaning445 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 445 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 227 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [226]) + (countLit q [227]) := List.countP_append (p := literal q) (l₁ := [226]) (l₂ := [227])
  have hm := merge_two (literal (valuationOf q) (226)) (literal (valuationOf q) (227)) (literal (valuationOf q) (446)) (countLit q [226]) (countLit q [227]) (count445 q) 1 1 (meaning226 q) (meaning227 q) (meaning446 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 227 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 227 = false ∨ valuation q 446 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [224, 225]) + (countLit q [226, 227]) := List.countP_append (p := literal q) (l₁ := [224, 225]) (l₂ := [226, 227])
  have hm := merge_right (literal (valuationOf q) (445)) (literal (valuationOf q) (447)) (countLit q [224, 225]) (countLit q [226, 227]) (count447 q) 1 (meaning445 q) (meaning447 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 447 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 446 = false ∨ valuationOf q 448 = true := by
  have hs : count447 q = (countLit q [224, 225]) + (countLit q [226, 227]) := List.countP_append (p := literal q) (l₁ := [224, 225]) (l₂ := [226, 227])
  have hm := merge_right (literal (valuationOf q) (446)) (literal (valuationOf q) (448)) (countLit q [224, 225]) (countLit q [226, 227]) (count447 q) 2 (meaning446 q) (meaning448 q) hs
  change valuationOf q 446 = false ∨ valuationOf q 448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 446 = false ∨ valuation q 448 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E055.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112055
