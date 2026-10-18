import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_right (literal (valuationOf q) (147)) (literal (valuationOf q) (283)) (countLit q [146]) (countLit q [147]) (count283 q) 1 (meaning147 q) (meaning283 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 283 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [148]) + (countLit q [149]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149])
  have hm := merge_right (literal (valuationOf q) (149)) (literal (valuationOf q) (285)) (countLit q [148]) (countLit q [149]) (count285 q) 1 (meaning149 q) (meaning285 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 285 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [146, 147]) + (countLit q [148, 149]) := List.countP_append (p := literal q) (l₁ := [146, 147]) (l₂ := [148, 149])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [146, 147]) (countLit q [148, 149]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [146, 147]) + (countLit q [148, 149]) := List.countP_append (p := literal q) (l₁ := [146, 147]) (l₂ := [148, 149])
  have hm := merge_left (literal (valuationOf q) (283)) (literal (valuationOf q) (287)) (countLit q [146, 147]) (countLit q [148, 149]) (count287 q) 1 (meaning283 q) (meaning287 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 287 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [143, 144, 145]) + (countLit q [146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145]) (l₂ := [146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [143, 144, 145]) (countLit q [146, 147, 148, 149]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [143, 144, 145]) + (countLit q [146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145]) (l₂ := [146, 147, 148, 149])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (289)) (countLit q [143, 144, 145]) (countLit q [146, 147, 148, 149]) (count289 q) 1 (meaning281 q) (meaning289 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 289 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149])
  have hm := merge_left (literal (valuationOf q) (277)) (literal (valuationOf q) (291)) (countLit q [137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149]) (count291 q) 1 (meaning277 q) (meaning291 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 291 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_left (literal (valuationOf q) (267)) (literal (valuationOf q) (293)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count293 q) 1 (meaning267 q) (meaning293 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 293 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_two (literal (valuationOf q) (267)) (literal (valuationOf q) (291)) (literal (valuationOf q) (294)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count293 q) 1 1 (meaning267 q) (meaning291 q) (meaning294 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 291 = false ∨ valuation q 294 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (294)) (literal (valuationOf q) (296)) (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count295 q) 2 (meaning294 q) (meaning296 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 296 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (295)) (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count295 q) 1 (meaning245 q) (meaning295 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 295 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_two (literal (valuationOf q) (245)) (literal (valuationOf q) (293)) (literal (valuationOf q) (296)) (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count295 q) 1 1 (meaning245 q) (meaning293 q) (meaning296 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 293 = false ∨ valuation q 296 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 246 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_left (literal (valuationOf q) (246)) (literal (valuationOf q) (296)) (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count295 q) 2 (meaning246 q) (meaning296 q) hs
  change valuationOf q 246 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 296 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_left (literal (valuationOf q) (151)) (literal (valuationOf q) (297)) (countLit q [151]) (countLit q [152]) (count297 q) 1 (meaning151 q) (meaning297 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 297 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151, 152])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [150]) (countLit q [151, 152]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [154]) + (countLit q [155]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155])
  have hm := merge_left (literal (valuationOf q) (154)) (literal (valuationOf q) (301)) (countLit q [154]) (countLit q [155]) (count301 q) 1 (meaning154 q) (meaning301 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 301 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154, 155])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [153]) (countLit q [154, 155]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 153 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154, 155])
  have hm := merge_left (literal (valuationOf q) (153)) (literal (valuationOf q) (303)) (countLit q [153]) (countLit q [154, 155]) (count303 q) 1 (meaning153 q) (meaning303 q) hs
  change valuationOf q 153 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 303 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [150, 151, 152]) + (countLit q [153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152]) (l₂ := [153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [150, 151, 152]) (countLit q [153, 154, 155]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 303 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [150, 151, 152]) + (countLit q [153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152]) (l₂ := [153, 154, 155])
  have hm := merge_two (literal (valuationOf q) (299)) (literal (valuationOf q) (303)) (literal (valuationOf q) (306)) (countLit q [150, 151, 152]) (countLit q [153, 154, 155]) (count305 q) 1 1 (meaning299 q) (meaning303 q) (meaning306 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 303 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 303 = false ∨ valuation q 306 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 156 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157, 158])
  have hm := merge_left (literal (valuationOf q) (156)) (literal (valuationOf q) (309)) (countLit q [156]) (countLit q [157, 158]) (count309 q) 1 (meaning156 q) (meaning309 q) hs
  change valuationOf q 156 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 309 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [156, 157, 158]) + (countLit q [159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158]) (l₂ := [159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (309)) (literal (valuationOf q) (315)) (countLit q [156, 157, 158]) (countLit q [159, 160, 161]) (count315 q) 1 (meaning309 q) (meaning315 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 315 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (317)) (countLit q [150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161]) (count317 q) 1 (meaning305 q) (meaning317 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 317 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 306 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (306)) (literal (valuationOf q) (318)) (countLit q [150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161]) (count317 q) 2 (meaning306 q) (meaning318 q) hs
  change valuationOf q 306 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 306 = false ∨ valuation q 318 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_right (literal (valuationOf q) (164)) (literal (valuationOf q) (319)) (countLit q [163]) (countLit q [164]) (count319 q) 1 (meaning164 q) (meaning319 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 319 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163, 164])
  have hm := merge_right (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (countLit q [162]) (countLit q [163, 164]) (count321 q) 1 (meaning319 q) (meaning321 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163, 164])
  have hm := merge_left (literal (valuationOf q) (162)) (literal (valuationOf q) (321)) (countLit q [162]) (countLit q [163, 164]) (count321 q) 1 (meaning162 q) (meaning321 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 321 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [166]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [168])
  have hm := merge_left (literal (valuationOf q) (166)) (literal (valuationOf q) (323)) (countLit q [166]) (countLit q [168]) (count323 q) 1 (meaning166 q) (meaning323 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 323 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E147.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112147
