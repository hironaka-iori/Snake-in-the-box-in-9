import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [203, 204]) + (countLit q [205, 206]) := List.countP_append (p := literal q) (l₁ := [203, 204]) (l₂ := [205, 206])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (401)) (countLit q [203, 204]) (countLit q [205, 206]) (count401 q) 1 (meaning397 q) (meaning401 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 401 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [199, 200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [199, 200, 201, 202]) (countLit q [203, 204, 205, 206]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [199, 200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (403)) (countLit q [199, 200, 201, 202]) (countLit q [203, 204, 205, 206]) (count403 q) 1 (meaning395 q) (meaning403 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 403 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [199, 200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_two (literal (valuationOf q) (395)) (literal (valuationOf q) (401)) (literal (valuationOf q) (404)) (countLit q [199, 200, 201, 202]) (countLit q [203, 204, 205, 206]) (count403 q) 1 1 (meaning395 q) (meaning401 q) (meaning404 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 401 = false ∨ valuation q 404 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 396 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [199, 200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (396)) (literal (valuationOf q) (404)) (countLit q [199, 200, 201, 202]) (countLit q [203, 204, 205, 206]) (count403 q) 2 (meaning396 q) (meaning404 q) hs
  change valuationOf q 396 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 396 = false ∨ valuation q 404 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (404)) (literal (valuationOf q) (406)) (countLit q [192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 2 (meaning404 q) (meaning406 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 406 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (389)) (literal (valuationOf q) (405)) (countLit q [192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 1 (meaning389 q) (meaning405 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 405 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_two (literal (valuationOf q) (389)) (literal (valuationOf q) (403)) (literal (valuationOf q) (406)) (countLit q [192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 1 1 (meaning389 q) (meaning403 q) (meaning406 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 403 = false ∨ valuation q 406 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 210 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_right (literal (valuationOf q) (210)) (literal (valuationOf q) (409)) (countLit q [209]) (countLit q [210]) (count409 q) 1 (meaning210 q) (meaning409 q) hs
  change valuationOf q 210 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 409 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [207, 208]) + (countLit q [209, 210]) := List.countP_append (p := literal q) (l₁ := [207, 208]) (l₂ := [209, 210])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [207, 208]) (countLit q [209, 210]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [211]) + (countLit q [212]) := List.countP_append (p := literal q) (l₁ := [211]) (l₂ := [212])
  have hm := merge_right (literal (valuationOf q) (212)) (literal (valuationOf q) (413)) (countLit q [211]) (countLit q [212]) (count413 q) 1 (meaning212 q) (meaning413 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 413 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [211, 212]) + (countLit q [213, 214]) := List.countP_append (p := literal q) (l₁ := [211, 212]) (l₂ := [213, 214])
  have hm := merge_left (literal (valuationOf q) (413)) (literal (valuationOf q) (417)) (countLit q [211, 212]) (countLit q [213, 214]) (count417 q) 1 (meaning413 q) (meaning417 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 417 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [207, 208, 209, 210]) + (countLit q [211, 212, 213, 214]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210]) (l₂ := [211, 212, 213, 214])
  have hm := merge_right (literal (valuationOf q) (417)) (literal (valuationOf q) (419)) (countLit q [207, 208, 209, 210]) (countLit q [211, 212, 213, 214]) (count419 q) 1 (meaning417 q) (meaning419 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [207, 208, 209, 210]) + (countLit q [211, 212, 213, 214]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210]) (l₂ := [211, 212, 213, 214])
  have hm := merge_left (literal (valuationOf q) (411)) (literal (valuationOf q) (419)) (countLit q [207, 208, 209, 210]) (countLit q [211, 212, 213, 214]) (count419 q) 1 (meaning411 q) (meaning419 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 419 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 216 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [215]) + (countLit q [216]) := List.countP_append (p := literal q) (l₁ := [215]) (l₂ := [216])
  have hm := merge_right (literal (valuationOf q) (216)) (literal (valuationOf q) (421)) (countLit q [215]) (countLit q [216]) (count421 q) 1 (meaning216 q) (meaning421 q) hs
  change valuationOf q 216 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 421 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [215]) + (countLit q [216]) := List.countP_append (p := literal q) (l₁ := [215]) (l₂ := [216])
  have hm := merge_left (literal (valuationOf q) (215)) (literal (valuationOf q) (421)) (countLit q [215]) (countLit q [216]) (count421 q) 1 (meaning215 q) (meaning421 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 421 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [215, 216]) + (countLit q [217, 218]) := List.countP_append (p := literal q) (l₁ := [215, 216]) (l₂ := [217, 218])
  have hm := merge_left (literal (valuationOf q) (421)) (literal (valuationOf q) (425)) (countLit q [215, 216]) (countLit q [217, 218]) (count425 q) 1 (meaning421 q) (meaning425 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 425 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [219]) + (countLit q [220]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220])
  have hm := merge_right (literal (valuationOf q) (220)) (literal (valuationOf q) (427)) (countLit q [219]) (countLit q [220]) (count427 q) 1 (meaning220 q) (meaning427 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 427 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [219]) + (countLit q [220]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220])
  have hm := merge_left (literal (valuationOf q) (219)) (literal (valuationOf q) (427)) (countLit q [219]) (countLit q [220]) (count427 q) 1 (meaning219 q) (meaning427 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 427 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [219, 220]) + (countLit q [221, 222]) := List.countP_append (p := literal q) (l₁ := [219, 220]) (l₂ := [221, 222])
  have hm := merge_left (literal (valuationOf q) (427)) (literal (valuationOf q) (431)) (countLit q [219, 220]) (countLit q [221, 222]) (count431 q) 1 (meaning427 q) (meaning431 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 431 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [215, 216, 217, 218]) + (countLit q [219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [215, 216, 217, 218]) (l₂ := [219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (431)) (literal (valuationOf q) (433)) (countLit q [215, 216, 217, 218]) (countLit q [219, 220, 221, 222]) (count433 q) 1 (meaning431 q) (meaning433 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 433 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [215, 216, 217, 218]) + (countLit q [219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [215, 216, 217, 218]) (l₂ := [219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (433)) (countLit q [215, 216, 217, 218]) (countLit q [219, 220, 221, 222]) (count433 q) 1 (meaning425 q) (meaning433 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 433 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [215, 216, 217, 218]) + (countLit q [219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [215, 216, 217, 218]) (l₂ := [219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (425)) (literal (valuationOf q) (431)) (literal (valuationOf q) (434)) (countLit q [215, 216, 217, 218]) (countLit q [219, 220, 221, 222]) (count433 q) 1 1 (meaning425 q) (meaning431 q) (meaning434 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 431 = false ∨ valuation q 434 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (433)) (literal (valuationOf q) (435)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 (meaning433 q) (meaning435 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 435 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 434 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (434)) (literal (valuationOf q) (436)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 2 (meaning434 q) (meaning436 q) hs
  change valuationOf q 434 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 434 = false ∨ valuation q 436 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (435)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 (meaning419 q) (meaning435 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 435 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (419)) (literal (valuationOf q) (433)) (literal (valuationOf q) (436)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 1 (meaning419 q) (meaning433 q) (meaning436 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 433 = false ∨ valuation q 436 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 436 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (436)) (literal (valuationOf q) (438)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 2 (meaning436 q) (meaning438 q) hs
  change valuationOf q 436 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 436 = false ∨ valuation q 438 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (437)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 (meaning405 q) (meaning437 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 437 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 435 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (405)) (literal (valuationOf q) (435)) (literal (valuationOf q) (438)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 1 (meaning405 q) (meaning435 q) (meaning438 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 435 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 435 = false ∨ valuation q 438 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E052.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112052
