import E112079Semantics
import B112E079Inputs
namespace Snake9.Regrowth.E112079
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 268 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137])
  have hm := merge_right (literal (valuationOf q) (268)) (literal (valuationOf q) (270)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137]) (count269 q) 2 (meaning268 q) (meaning270 q) hs
  change valuationOf q 268 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 268 = false ∨ valuation q 270 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (269)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137]) (count269 q) 1 (meaning255 q) (meaning269 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 269 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137])
  have hm := merge_two (literal (valuationOf q) (255)) (literal (valuationOf q) (267)) (literal (valuationOf q) (270)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137]) (count269 q) 1 1 (meaning255 q) (meaning267 q) (meaning270 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 267 = false ∨ valuation q 270 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 270 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_right (literal (valuationOf q) (270)) (literal (valuationOf q) (272)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 2 (meaning270 q) (meaning272 q) hs
  change valuationOf q 270 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 270 = false ∨ valuation q 272 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (271)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 1 (meaning243 q) (meaning271 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 271 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_two (literal (valuationOf q) (243)) (literal (valuationOf q) (269)) (literal (valuationOf q) (272)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 1 1 (meaning243 q) (meaning269 q) (meaning272 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 269 = false ∨ valuation q 272 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_right (literal (valuationOf q) (140)) (literal (valuationOf q) (273)) (countLit q [139]) (countLit q [140]) (count273 q) 1 (meaning140 q) (meaning273 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 273 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139, 140])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [138]) (countLit q [139, 140]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139, 140])
  have hm := merge_left (literal (valuationOf q) (138)) (literal (valuationOf q) (275)) (countLit q [138]) (countLit q [139, 140]) (count275 q) 1 (meaning138 q) (meaning275 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 275 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139, 140])
  have hm := merge_two (literal (valuationOf q) (138)) (literal (valuationOf q) (273)) (literal (valuationOf q) (276)) (countLit q [138]) (countLit q [139, 140]) (count275 q) 1 1 (meaning138 q) (meaning273 q) (meaning276 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 273 = false ∨ valuation q 276 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (281)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143]) (count281 q) 1 (meaning275 q) (meaning281 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 281 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 276 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143])
  have hm := merge_left (literal (valuationOf q) (276)) (literal (valuationOf q) (282)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143]) (count281 q) 2 (meaning276 q) (meaning282 q) hs
  change valuationOf q 276 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 276 = false ∨ valuation q 282 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_right (literal (valuationOf q) (146)) (literal (valuationOf q) (283)) (countLit q [145]) (countLit q [146]) (count283 q) 1 (meaning146 q) (meaning283 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 283 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145, 146])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [144]) (countLit q [145, 146]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_left (literal (valuationOf q) (147)) (literal (valuationOf q) (287)) (countLit q [147]) (countLit q [148]) (count287 q) 1 (meaning147 q) (meaning287 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 287 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_right (literal (valuationOf q) (150)) (literal (valuationOf q) (289)) (countLit q [149]) (countLit q [150]) (count289 q) 1 (meaning150 q) (meaning289 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 289 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [147, 148]) (countLit q [149, 150]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_left (literal (valuationOf q) (287)) (literal (valuationOf q) (291)) (countLit q [147, 148]) (countLit q [149, 150]) (count291 q) 1 (meaning287 q) (meaning291 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 291 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [144, 145, 146]) (countLit q [147, 148, 149, 150]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (293)) (countLit q [144, 145, 146]) (countLit q [147, 148, 149, 150]) (count293 q) 1 (meaning285 q) (meaning293 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 293 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_two (literal (valuationOf q) (285)) (literal (valuationOf q) (291)) (literal (valuationOf q) (294)) (countLit q [144, 145, 146]) (countLit q [147, 148, 149, 150]) (count293 q) 1 1 (meaning285 q) (meaning291 q) (meaning294 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 291 = false ∨ valuation q 294 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150])
  have hm := merge_right (literal (valuationOf q) (294)) (literal (valuationOf q) (296)) (countLit q [138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150]) (count295 q) 2 (meaning294 q) (meaning296 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 296 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (295)) (countLit q [138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150]) (count295 q) 1 (meaning281 q) (meaning295 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 295 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150])
  have hm := merge_two (literal (valuationOf q) (281)) (literal (valuationOf q) (293)) (literal (valuationOf q) (296)) (countLit q [138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150]) (count295 q) 1 1 (meaning281 q) (meaning293 q) (meaning296 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 293 = false ∨ valuation q 296 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 282 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150])
  have hm := merge_left (literal (valuationOf q) (282)) (literal (valuationOf q) (296)) (countLit q [138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150]) (count295 q) 2 (meaning282 q) (meaning296 q) hs
  change valuationOf q 282 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 282 = false ∨ valuation q 296 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [152]) + (countLit q [153]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153])
  have hm := merge_left (literal (valuationOf q) (152)) (literal (valuationOf q) (297)) (countLit q [152]) (countLit q [153]) (count297 q) 1 (meaning152 q) (meaning297 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 297 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [151]) + (countLit q [152, 153]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152, 153])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [151]) (countLit q [152, 153]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [154]) + (countLit q [155]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155])
  have hm := merge_right (literal (valuationOf q) (155)) (literal (valuationOf q) (301)) (countLit q [154]) (countLit q [155]) (count301 q) 1 (meaning155 q) (meaning301 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 301 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [156]) + (countLit q [157]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157])
  have hm := merge_right (literal (valuationOf q) (157)) (literal (valuationOf q) (303)) (countLit q [156]) (countLit q [157]) (count303 q) 1 (meaning157 q) (meaning303 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 303 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [154, 155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [154, 155]) (l₂ := [156, 157])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [154, 155]) (countLit q [156, 157]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E079.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112079
