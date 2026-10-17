import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [139, 140, 141]) + (countLit q [142, 143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141]) (l₂ := [142, 143, 144, 145])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (283)) (countLit q [139, 140, 141]) (countLit q [142, 143, 144, 145]) (count283 q) 1 (meaning275 q) (meaning283 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 283 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (285)) (countLit q [133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145]) (count285 q) 1 (meaning271 q) (meaning285 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 285 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 283 = false ∨ valuationOf q 286 = true := by
  have hs : count285 q = (countLit q [133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145])
  have hm := merge_two (literal (valuationOf q) (271)) (literal (valuationOf q) (283)) (literal (valuationOf q) (286)) (countLit q [133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145]) (count285 q) 1 1 (meaning271 q) (meaning283 q) (meaning286 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 283 = false ∨ valuationOf q 286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 283 = false ∨ valuation q 286 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 272 = false ∨ valuationOf q 286 = true := by
  have hs : count285 q = (countLit q [133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145])
  have hm := merge_left (literal (valuationOf q) (272)) (literal (valuationOf q) (286)) (countLit q [133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145]) (count285 q) 2 (meaning272 q) (meaning286 q) hs
  change valuationOf q 272 = false ∨ valuationOf q 286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 286 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_right (literal (valuationOf q) (148)) (literal (valuationOf q) (287)) (countLit q [147]) (countLit q [148]) (count287 q) 1 (meaning148 q) (meaning287 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 287 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_left (literal (valuationOf q) (147)) (literal (valuationOf q) (287)) (countLit q [147]) (countLit q [148]) (count287 q) 1 (meaning147 q) (meaning287 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 287 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147, 148])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [146]) (countLit q [147, 148]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147, 148])
  have hm := merge_left (literal (valuationOf q) (146)) (literal (valuationOf q) (289)) (countLit q [146]) (countLit q [147, 148]) (count289 q) 1 (meaning146 q) (meaning289 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 289 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 287 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147, 148])
  have hm := merge_two (literal (valuationOf q) (146)) (literal (valuationOf q) (287)) (literal (valuationOf q) (290)) (countLit q [146]) (countLit q [147, 148]) (count289 q) 1 1 (meaning146 q) (meaning287 q) (meaning290 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 287 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 287 = false ∨ valuation q 290 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_right (literal (valuationOf q) (151)) (literal (valuationOf q) (291)) (countLit q [150]) (countLit q [151]) (count291 q) 1 (meaning151 q) (meaning291 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 291 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_left (literal (valuationOf q) (150)) (literal (valuationOf q) (291)) (countLit q [150]) (countLit q [151]) (count291 q) 1 (meaning150 q) (meaning291 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 291 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 151 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_two (literal (valuationOf q) (150)) (literal (valuationOf q) (151)) (literal (valuationOf q) (292)) (countLit q [150]) (countLit q [151]) (count291 q) 1 1 (meaning150 q) (meaning151 q) (meaning292 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 151 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 151 = false ∨ valuation q 292 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150, 151])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [149]) (countLit q [150, 151]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 292 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150, 151])
  have hm := merge_right (literal (valuationOf q) (292)) (literal (valuationOf q) (294)) (countLit q [149]) (countLit q [150, 151]) (count293 q) 2 (meaning292 q) (meaning294 q) hs
  change valuationOf q 292 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 292 = false ∨ valuation q 294 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [146, 147, 148]) + (countLit q [149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148]) (l₂ := [149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [146, 147, 148]) (countLit q [149, 150, 151]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [146, 147, 148]) + (countLit q [149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148]) (l₂ := [149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (294)) (literal (valuationOf q) (296)) (countLit q [146, 147, 148]) (countLit q [149, 150, 151]) (count295 q) 2 (meaning294 q) (meaning296 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 296 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [146, 147, 148]) + (countLit q [149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148]) (l₂ := [149, 150, 151])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (295)) (countLit q [146, 147, 148]) (countLit q [149, 150, 151]) (count295 q) 1 (meaning289 q) (meaning295 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 295 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [146, 147, 148]) + (countLit q [149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148]) (l₂ := [149, 150, 151])
  have hm := merge_two (literal (valuationOf q) (289)) (literal (valuationOf q) (293)) (literal (valuationOf q) (296)) (countLit q [146, 147, 148]) (countLit q [149, 150, 151]) (count295 q) 1 1 (meaning289 q) (meaning293 q) (meaning296 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 293 = false ∨ valuation q 296 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 290 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [146, 147, 148]) + (countLit q [149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148]) (l₂ := [149, 150, 151])
  have hm := merge_left (literal (valuationOf q) (290)) (literal (valuationOf q) (296)) (countLit q [146, 147, 148]) (countLit q [149, 150, 151]) (count295 q) 2 (meaning290 q) (meaning296 q) hs
  change valuationOf q 290 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 290 = false ∨ valuation q 296 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [153]) + (countLit q [154]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154])
  have hm := merge_right (literal (valuationOf q) (154)) (literal (valuationOf q) (297)) (countLit q [153]) (countLit q [154]) (count297 q) 1 (meaning154 q) (meaning297 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 297 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153, 154])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [152]) (countLit q [153, 154]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [155]) + (countLit q [156]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156])
  have hm := merge_left (literal (valuationOf q) (155)) (literal (valuationOf q) (301)) (countLit q [155]) (countLit q [156]) (count301 q) 1 (meaning155 q) (meaning301 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 301 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_right (literal (valuationOf q) (158)) (literal (valuationOf q) (303)) (countLit q [157]) (countLit q [158]) (count303 q) 1 (meaning158 q) (meaning303 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 303 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [155, 156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [155, 156]) (l₂ := [157, 158])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [155, 156]) (countLit q [157, 158]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [155, 156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [155, 156]) (l₂ := [157, 158])
  have hm := merge_left (literal (valuationOf q) (301)) (literal (valuationOf q) (305)) (countLit q [155, 156]) (countLit q [157, 158]) (count305 q) 1 (meaning301 q) (meaning305 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 305 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [152, 153, 154]) (countLit q [155, 156, 157, 158]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (299)) (literal (valuationOf q) (307)) (countLit q [152, 153, 154]) (countLit q [155, 156, 157, 158]) (count307 q) 1 (meaning299 q) (meaning307 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 307 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (309)) (countLit q [146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158]) (count309 q) 1 (meaning295 q) (meaning309 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 309 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 307 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158])
  have hm := merge_two (literal (valuationOf q) (295)) (literal (valuationOf q) (307)) (literal (valuationOf q) (310)) (countLit q [146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158]) (count309 q) 1 1 (meaning295 q) (meaning307 q) (meaning310 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 307 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 307 = false ∨ valuation q 310 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 296 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (296)) (literal (valuationOf q) (310)) (countLit q [146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158]) (count309 q) 2 (meaning296 q) (meaning310 q) hs
  change valuationOf q 296 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 296 = false ∨ valuation q 310 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E091.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112091
