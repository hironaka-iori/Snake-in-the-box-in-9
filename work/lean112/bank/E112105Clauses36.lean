import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 393 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201])
  have hm := merge_two (literal (valuationOf q) (379)) (literal (valuationOf q) (393)) (literal (valuationOf q) (396)) (countLit q [187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) (count395 q) 1 1 (meaning379 q) (meaning393 q) (meaning396 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 393 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 393 = false ∨ valuation q 396 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 380 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201])
  have hm := merge_left (literal (valuationOf q) (380)) (literal (valuationOf q) (396)) (countLit q [187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) (count395 q) 2 (meaning380 q) (meaning396 q) hs
  change valuationOf q 380 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 396 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [202]) + (countLit q [203]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203])
  have hm := merge_left (literal (valuationOf q) (202)) (literal (valuationOf q) (397)) (countLit q [202]) (countLit q [203]) (count397 q) 1 (meaning202 q) (meaning397 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 397 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [204]) + (countLit q [205]) := List.countP_append (p := literal q) (l₁ := [204]) (l₂ := [205])
  have hm := merge_right (literal (valuationOf q) (205)) (literal (valuationOf q) (399)) (countLit q [204]) (countLit q [205]) (count399 q) 1 (meaning205 q) (meaning399 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 399 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [202, 203]) (countLit q [204, 205]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (401)) (countLit q [202, 203]) (countLit q [204, 205]) (count401 q) 1 (meaning397 q) (meaning401 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 401 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 207 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [206]) + (countLit q [207]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207])
  have hm := merge_right (literal (valuationOf q) (207)) (literal (valuationOf q) (403)) (countLit q [206]) (countLit q [207]) (count403 q) 1 (meaning207 q) (meaning403 q) hs
  change valuationOf q 207 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 403 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (405)) (countLit q [208]) (countLit q [209]) (count405 q) 1 (meaning209 q) (meaning405 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 405 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [206, 207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 209])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [206, 207]) (countLit q [208, 209]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [206, 207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 209])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (407)) (countLit q [206, 207]) (countLit q [208, 209]) (count407 q) 1 (meaning403 q) (meaning407 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 407 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = false ∨ valuationOf q 408 = true := by
  have hs : count407 q = (countLit q [206, 207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 209])
  have hm := merge_two (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (literal (valuationOf q) (408)) (countLit q [206, 207]) (countLit q [208, 209]) (count407 q) 1 1 (meaning403 q) (meaning405 q) (meaning408 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = false ∨ valuationOf q 408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = false ∨ valuation q 408 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [202, 203, 204, 205]) + (countLit q [206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205]) (l₂ := [206, 207, 208, 209])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [202, 203, 204, 205]) (countLit q [206, 207, 208, 209]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 408 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [202, 203, 204, 205]) + (countLit q [206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205]) (l₂ := [206, 207, 208, 209])
  have hm := merge_right (literal (valuationOf q) (408)) (literal (valuationOf q) (410)) (countLit q [202, 203, 204, 205]) (countLit q [206, 207, 208, 209]) (count409 q) 2 (meaning408 q) (meaning410 q) hs
  change valuationOf q 408 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 408 = false ∨ valuation q 410 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [202, 203, 204, 205]) + (countLit q [206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205]) (l₂ := [206, 207, 208, 209])
  have hm := merge_left (literal (valuationOf q) (401)) (literal (valuationOf q) (409)) (countLit q [202, 203, 204, 205]) (countLit q [206, 207, 208, 209]) (count409 q) 1 (meaning401 q) (meaning409 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 409 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [202, 203, 204, 205]) + (countLit q [206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205]) (l₂ := [206, 207, 208, 209])
  have hm := merge_two (literal (valuationOf q) (401)) (literal (valuationOf q) (407)) (literal (valuationOf q) (410)) (countLit q [202, 203, 204, 205]) (countLit q [206, 207, 208, 209]) (count409 q) 1 1 (meaning401 q) (meaning407 q) (meaning410 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 407 = false ∨ valuation q 410 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (413)) (countLit q [212]) (countLit q [213]) (count413 q) 1 (meaning213 q) (meaning413 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 413 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_left (literal (valuationOf q) (212)) (literal (valuationOf q) (413)) (countLit q [212]) (countLit q [213]) (count413 q) 1 (meaning212 q) (meaning413 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 413 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [210, 211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [210, 211]) (l₂ := [212, 213])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [210, 211]) (countLit q [212, 213]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (417)) (countLit q [214]) (countLit q [215]) (count417 q) 1 (meaning215 q) (meaning417 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 417 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [216]) + (countLit q [217]) := List.countP_append (p := literal q) (l₁ := [216]) (l₂ := [217])
  have hm := merge_right (literal (valuationOf q) (217)) (literal (valuationOf q) (419)) (countLit q [216]) (countLit q [217]) (count419 q) 1 (meaning217 q) (meaning419 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 419 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_right (literal (valuationOf q) (419)) (literal (valuationOf q) (421)) (countLit q [214, 215]) (countLit q [216, 217]) (count421 q) 1 (meaning419 q) (meaning421 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 421 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (421)) (countLit q [214, 215]) (countLit q [216, 217]) (count421 q) 1 (meaning417 q) (meaning421 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 421 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 419 = false ∨ valuationOf q 422 = true := by
  have hs : count421 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_two (literal (valuationOf q) (417)) (literal (valuationOf q) (419)) (literal (valuationOf q) (422)) (countLit q [214, 215]) (countLit q [216, 217]) (count421 q) 1 1 (meaning417 q) (meaning419 q) (meaning422 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 419 = false ∨ valuationOf q 422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = false ∨ valuation q 422 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [210, 211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (countLit q [210, 211, 212, 213]) (countLit q [214, 215, 216, 217]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 422 = false ∨ valuationOf q 424 = true := by
  have hs : count423 q = (countLit q [210, 211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (422)) (literal (valuationOf q) (424)) (countLit q [210, 211, 212, 213]) (countLit q [214, 215, 216, 217]) (count423 q) 2 (meaning422 q) (meaning424 q) hs
  change valuationOf q 422 = false ∨ valuationOf q 424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 422 = false ∨ valuation q 424 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [210, 211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (415)) (literal (valuationOf q) (423)) (countLit q [210, 211, 212, 213]) (countLit q [214, 215, 216, 217]) (count423 q) 1 (meaning415 q) (meaning423 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 423 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 421 = false ∨ valuationOf q 424 = true := by
  have hs : count423 q = (countLit q [210, 211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_two (literal (valuationOf q) (415)) (literal (valuationOf q) (421)) (literal (valuationOf q) (424)) (countLit q [210, 211, 212, 213]) (countLit q [214, 215, 216, 217]) (count423 q) 1 1 (meaning415 q) (meaning421 q) (meaning424 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 421 = false ∨ valuationOf q 424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 421 = false ∨ valuation q 424 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 424 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (424)) (literal (valuationOf q) (426)) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) (count425 q) 2 (meaning424 q) (meaning426 q) hs
  change valuationOf q 424 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 424 = false ∨ valuation q 426 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (409)) (literal (valuationOf q) (425)) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) (count425 q) 1 (meaning409 q) (meaning425 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 425 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 423 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_two (literal (valuationOf q) (409)) (literal (valuationOf q) (423)) (literal (valuationOf q) (426)) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) (count425 q) 1 1 (meaning409 q) (meaning423 q) (meaning426 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 423 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 423 = false ∨ valuation q 426 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (410)) (literal (valuationOf q) (426)) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) (count425 q) 2 (meaning410 q) (meaning426 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 426 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E105.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112105
