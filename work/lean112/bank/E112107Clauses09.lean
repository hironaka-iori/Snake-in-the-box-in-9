import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 270 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (270)) (literal (valuationOf q) (272)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (count271 q) 2 (meaning270 q) (meaning272 q) hs
  change valuationOf q 270 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 270 = false ∨ valuation q 272 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (271)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (count271 q) 1 (meaning243 q) (meaning271 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 271 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138])
  have hm := merge_two (literal (valuationOf q) (243)) (literal (valuationOf q) (269)) (literal (valuationOf q) (272)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (count271 q) 1 1 (meaning243 q) (meaning269 q) (meaning272 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 269 = false ∨ valuation q 272 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (244)) (literal (valuationOf q) (272)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (count271 q) 2 (meaning244 q) (meaning272 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 272 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_right (literal (valuationOf q) (141)) (literal (valuationOf q) (273)) (countLit q [140]) (countLit q [141]) (count273 q) 1 (meaning141 q) (meaning273 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 273 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_left (literal (valuationOf q) (140)) (literal (valuationOf q) (273)) (countLit q [140]) (countLit q [141]) (count273 q) 1 (meaning140 q) (meaning273 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 273 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [139]) + (countLit q [140, 141]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140, 141])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [139]) (countLit q [140, 141]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [139, 140, 141]) + (countLit q [142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141]) (l₂ := [142, 143, 144])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (281)) (countLit q [139, 140, 141]) (countLit q [142, 143, 144]) (count281 q) 1 (meaning275 q) (meaning281 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 281 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_right (literal (valuationOf q) (147)) (literal (valuationOf q) (283)) (countLit q [146]) (countLit q [147]) (count283 q) 1 (meaning147 q) (meaning283 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 283 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146, 147])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [145]) (countLit q [146, 147]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [148]) + (countLit q [149]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149])
  have hm := merge_right (literal (valuationOf q) (149)) (literal (valuationOf q) (287)) (countLit q [148]) (countLit q [149]) (count287 q) 1 (meaning149 q) (meaning287 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 287 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_left (literal (valuationOf q) (150)) (literal (valuationOf q) (289)) (countLit q [150]) (countLit q [151]) (count289 q) 1 (meaning150 q) (meaning289 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 289 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [148, 149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [148, 149]) (l₂ := [150, 151])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [148, 149]) (countLit q [150, 151]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [148, 149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [148, 149]) (l₂ := [150, 151])
  have hm := merge_left (literal (valuationOf q) (287)) (literal (valuationOf q) (291)) (countLit q [148, 149]) (countLit q [150, 151]) (count291 q) 1 (meaning287 q) (meaning291 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 291 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [145, 146, 147]) + (countLit q [148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147]) (l₂ := [148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [145, 146, 147]) (countLit q [148, 149, 150, 151]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [145, 146, 147]) + (countLit q [148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147]) (l₂ := [148, 149, 150, 151])
  have hm := merge_two (literal (valuationOf q) (285)) (literal (valuationOf q) (291)) (literal (valuationOf q) (294)) (countLit q [145, 146, 147]) (countLit q [148, 149, 150, 151]) (count293 q) 1 1 (meaning285 q) (meaning291 q) (meaning294 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 291 = false ∨ valuation q 294 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (294)) (literal (valuationOf q) (296)) (countLit q [139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151]) (count295 q) 2 (meaning294 q) (meaning296 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 296 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (295)) (countLit q [139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151]) (count295 q) 1 (meaning281 q) (meaning295 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 295 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 161 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161])
  have hm := merge_right (literal (valuationOf q) (161)) (literal (valuationOf q) (309)) (countLit q [160]) (countLit q [161]) (count309 q) 1 (meaning161 q) (meaning309 q) hs
  change valuationOf q 161 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 309 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161])
  have hm := merge_left (literal (valuationOf q) (160)) (literal (valuationOf q) (309)) (countLit q [160]) (countLit q [161]) (count309 q) 1 (meaning160 q) (meaning309 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 309 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160, 161])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [159]) (countLit q [160, 161]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160, 161])
  have hm := merge_left (literal (valuationOf q) (159)) (literal (valuationOf q) (311)) (countLit q [159]) (countLit q [160, 161]) (count311 q) 1 (meaning159 q) (meaning311 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 311 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160, 161])
  have hm := merge_two (literal (valuationOf q) (159)) (literal (valuationOf q) (309)) (literal (valuationOf q) (312)) (countLit q [159]) (countLit q [160, 161]) (count311 q) 1 1 (meaning159 q) (meaning309 q) (meaning312 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 309 = false ∨ valuation q 312 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [164]) + (countLit q [165]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165])
  have hm := merge_left (literal (valuationOf q) (164)) (literal (valuationOf q) (315)) (countLit q [164]) (countLit q [165]) (count315 q) 1 (meaning164 q) (meaning315 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 315 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [162, 163]) + (countLit q [164, 165]) := List.countP_append (p := literal q) (l₁ := [162, 163]) (l₂ := [164, 165])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [162, 163]) (countLit q [164, 165]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [159, 160, 161]) + (countLit q [162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161]) (l₂ := [162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [159, 160, 161]) (countLit q [162, 163, 164, 165]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [159, 160, 161]) + (countLit q [162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161]) (l₂ := [162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (319)) (countLit q [159, 160, 161]) (countLit q [162, 163, 164, 165]) (count319 q) 1 (meaning311 q) (meaning319 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 319 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 317 = false ∨ valuationOf q 320 = true := by
  have hs : count319 q = (countLit q [159, 160, 161]) + (countLit q [162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161]) (l₂ := [162, 163, 164, 165])
  have hm := merge_two (literal (valuationOf q) (311)) (literal (valuationOf q) (317)) (literal (valuationOf q) (320)) (countLit q [159, 160, 161]) (countLit q [162, 163, 164, 165]) (count319 q) 1 1 (meaning311 q) (meaning317 q) (meaning320 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 317 = false ∨ valuationOf q 320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 317 = false ∨ valuation q 320 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 312 = false ∨ valuationOf q 320 = true := by
  have hs : count319 q = (countLit q [159, 160, 161]) + (countLit q [162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161]) (l₂ := [162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (312)) (literal (valuationOf q) (320)) (countLit q [159, 160, 161]) (countLit q [162, 163, 164, 165]) (count319 q) 2 (meaning312 q) (meaning320 q) hs
  change valuationOf q 312 = false ∨ valuationOf q 320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 312 = false ∨ valuation q 320 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (countLit q [152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165]) (count321 q) 1 (meaning319 q) (meaning321 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E107.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112107
