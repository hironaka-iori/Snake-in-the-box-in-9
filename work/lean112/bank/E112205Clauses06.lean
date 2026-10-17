import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause193 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [119, 120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [119, 120]) (l₂ := [121, 122])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (237)) (countLit q [119, 120]) (countLit q [121, 122]) (count237 q) 1 (meaning233 q) (meaning237 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 237 = true := counterClause193 (baseVal q)

theorem counterClause194 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [116, 117, 118]) + (countLit q [119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [116, 117, 118]) (l₂ := [119, 120, 121, 122])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [116, 117, 118]) (countLit q [119, 120, 121, 122]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause194 (baseVal q)

theorem counterClause195 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [116, 117, 118]) + (countLit q [119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [116, 117, 118]) (l₂ := [119, 120, 121, 122])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (239)) (countLit q [116, 117, 118]) (countLit q [119, 120, 121, 122]) (count239 q) 1 (meaning231 q) (meaning239 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 239 = true := counterClause195 (baseVal q)

theorem counterClause196 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [110, 111, 112, 113, 114, 115]) + (countLit q [116, 117, 118, 119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115]) (l₂ := [116, 117, 118, 119, 120, 121, 122])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (countLit q [110, 111, 112, 113, 114, 115]) (countLit q [116, 117, 118, 119, 120, 121, 122]) (count241 q) 1 (meaning239 q) (meaning241 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = true := counterClause196 (baseVal q)

theorem counterClause197 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [110, 111, 112, 113, 114, 115]) + (countLit q [116, 117, 118, 119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115]) (l₂ := [116, 117, 118, 119, 120, 121, 122])
  have hm := merge_left (literal (valuationOf q) (227)) (literal (valuationOf q) (241)) (countLit q [110, 111, 112, 113, 114, 115]) (countLit q [116, 117, 118, 119, 120, 121, 122]) (count241 q) 1 (meaning227 q) (meaning241 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 241 = true := counterClause197 (baseVal q)

theorem counterClause198 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 242 = true := by
  have hs : count241 q = (countLit q [110, 111, 112, 113, 114, 115]) + (countLit q [116, 117, 118, 119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115]) (l₂ := [116, 117, 118, 119, 120, 121, 122])
  have hm := merge_left (literal (valuationOf q) (228)) (literal (valuationOf q) (242)) (countLit q [110, 111, 112, 113, 114, 115]) (countLit q [116, 117, 118, 119, 120, 121, 122]) (count241 q) 2 (meaning228 q) (meaning242 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 242 = true := counterClause198 (baseVal q)

theorem counterClause199 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [123]) + (countLit q [124, 125]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124, 125])
  have hm := merge_left (literal (valuationOf q) (123)) (literal (valuationOf q) (245)) (countLit q [123]) (countLit q [124, 125]) (count245 q) 1 (meaning123 q) (meaning245 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 245 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (253)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count253 q) 1 (meaning245 q) (meaning253 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 253 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_right (literal (valuationOf q) (134)) (literal (valuationOf q) (259)) (countLit q [133]) (countLit q [134]) (count259 q) 1 (meaning134 q) (meaning259 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 259 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [133, 134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [133, 134]) (l₂ := [135, 136])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (263)) (countLit q [133, 134]) (countLit q [135, 136]) (count263 q) 1 (meaning259 q) (meaning263 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 263 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [130, 131, 132]) + (countLit q [133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132]) (l₂ := [133, 134, 135, 136])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [130, 131, 132]) (countLit q [133, 134, 135, 136]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136])
  have hm := merge_right (literal (valuationOf q) (265)) (literal (valuationOf q) (267)) (countLit q [123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136]) (count267 q) 1 (meaning265 q) (meaning267 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 267 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (267)) (countLit q [123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136]) (count267 q) 1 (meaning253 q) (meaning267 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 267 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]) + (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]) (l₂ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136])
  have hm := merge_left (literal (valuationOf q) (241)) (literal (valuationOf q) (269)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (count269 q) 1 (meaning241 q) (meaning269 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 269 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]) + (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]) (l₂ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136])
  have hm := merge_two (literal (valuationOf q) (241)) (literal (valuationOf q) (267)) (literal (valuationOf q) (270)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (count269 q) 1 1 (meaning241 q) (meaning267 q) (meaning270 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 267 = false ∨ valuation q 270 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 242 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]) + (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]) (l₂ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136])
  have hm := merge_left (literal (valuationOf q) (242)) (literal (valuationOf q) (270)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (count269 q) 2 (meaning242 q) (meaning270 q) hs
  change valuationOf q 242 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 270 = true := counterClause208 (baseVal q)

theorem counterClause209 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_right (literal (valuationOf q) (147)) (literal (valuationOf q) (285)) (countLit q [146]) (countLit q [147]) (count285 q) 1 (meaning147 q) (meaning285 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 285 = true := counterClause209 (baseVal q)

theorem counterClause210 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [148]) + (countLit q [149]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149])
  have hm := merge_right (literal (valuationOf q) (149)) (literal (valuationOf q) (287)) (countLit q [148]) (countLit q [149]) (count287 q) 1 (meaning149 q) (meaning287 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 287 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [146, 147]) + (countLit q [148, 149]) := List.countP_append (p := literal q) (l₁ := [146, 147]) (l₂ := [148, 149])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [146, 147]) (countLit q [148, 149]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [146, 147]) + (countLit q [148, 149]) := List.countP_append (p := literal q) (l₁ := [146, 147]) (l₂ := [148, 149])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (289)) (countLit q [146, 147]) (countLit q [148, 149]) (count289 q) 1 (meaning285 q) (meaning289 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 289 = true := counterClause212 (baseVal q)

theorem counterClause213 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [143, 144, 145]) + (countLit q [146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145]) (l₂ := [146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [143, 144, 145]) (countLit q [146, 147, 148, 149]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause213 (baseVal q)

theorem counterClause214 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_right (literal (valuationOf q) (152)) (literal (valuationOf q) (295)) (countLit q [151]) (countLit q [152]) (count295 q) 1 (meaning152 q) (meaning295 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 295 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151, 152])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [150]) (countLit q [151, 152]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [153]) + (countLit q [154]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154])
  have hm := merge_right (literal (valuationOf q) (154)) (literal (valuationOf q) (299)) (countLit q [153]) (countLit q [154]) (count299 q) 1 (meaning154 q) (meaning299 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 299 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [155]) + (countLit q [156]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156])
  have hm := merge_left (literal (valuationOf q) (155)) (literal (valuationOf q) (301)) (countLit q [155]) (countLit q [156]) (count301 q) 1 (meaning155 q) (meaning301 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 301 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [153, 154]) + (countLit q [155, 156]) := List.countP_append (p := literal q) (l₁ := [153, 154]) (l₂ := [155, 156])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [153, 154]) (countLit q [155, 156]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause219 (baseVal q)

theorem counterClause220 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [153, 154]) + (countLit q [155, 156]) := List.countP_append (p := literal q) (l₁ := [153, 154]) (l₂ := [155, 156])
  have hm := merge_left (literal (valuationOf q) (299)) (literal (valuationOf q) (303)) (countLit q [153, 154]) (countLit q [155, 156]) (count303 q) 1 (meaning299 q) (meaning303 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 303 = true := counterClause220 (baseVal q)

theorem counterClause221 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [150, 151, 152]) + (countLit q [153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152]) (l₂ := [153, 154, 155, 156])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [150, 151, 152]) (countLit q [153, 154, 155, 156]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause221 (baseVal q)

theorem counterClause222 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [150, 151, 152]) + (countLit q [153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152]) (l₂ := [153, 154, 155, 156])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (305)) (countLit q [150, 151, 152]) (countLit q [153, 154, 155, 156]) (count305 q) 1 (meaning297 q) (meaning305 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 305 = true := counterClause222 (baseVal q)

theorem counterClause223 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_left (literal (valuationOf q) (158)) (literal (valuationOf q) (307)) (countLit q [158]) (countLit q [159]) (count307 q) 1 (meaning158 q) (meaning307 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 307 = true := counterClause223 (baseVal q)

theorem counterClause224 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158, 159])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [157]) (countLit q [158, 159]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause224 (baseVal q)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E205.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112205
