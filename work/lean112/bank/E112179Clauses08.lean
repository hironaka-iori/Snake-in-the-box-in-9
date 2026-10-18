import E112179Semantics
import B112E179Inputs
namespace Snake9.Regrowth.E112179
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (277)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141, 142]) (count277 q) 1 (meaning269 q) (meaning277 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 277 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 275 = false ∨ valuationOf q 278 = true := by
  have hs : count277 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141, 142])
  have hm := merge_two (literal (valuationOf q) (269)) (literal (valuationOf q) (275)) (literal (valuationOf q) (278)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141, 142]) (count277 q) 1 1 (meaning269 q) (meaning275 q) (meaning278 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 275 = false ∨ valuationOf q 278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 275 = false ∨ valuation q 278 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 278 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (278)) (literal (valuationOf q) (280)) (countLit q [130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142]) (count279 q) 2 (meaning278 q) (meaning280 q) hs
  change valuationOf q 278 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 278 = false ∨ valuation q 280 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (279)) (countLit q [130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142]) (count279 q) 1 (meaning265 q) (meaning279 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 279 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (277)) (literal (valuationOf q) (280)) (countLit q [130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142]) (count279 q) 1 1 (meaning265 q) (meaning277 q) (meaning280 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 277 = false ∨ valuation q 280 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [144]) + (countLit q [145]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145])
  have hm := merge_right (literal (valuationOf q) (145)) (literal (valuationOf q) (281)) (countLit q [144]) (countLit q [145]) (count281 q) 1 (meaning145 q) (meaning281 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 281 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [143]) + (countLit q [144, 145]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144, 145])
  have hm := merge_right (literal (valuationOf q) (281)) (literal (valuationOf q) (283)) (countLit q [143]) (countLit q [144, 145]) (count283 q) 1 (meaning281 q) (meaning283 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_right (literal (valuationOf q) (148)) (literal (valuationOf q) (285)) (countLit q [147]) (countLit q [148]) (count285 q) 1 (meaning148 q) (meaning285 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 285 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_left (literal (valuationOf q) (147)) (literal (valuationOf q) (285)) (countLit q [147]) (countLit q [148]) (count285 q) 1 (meaning147 q) (meaning285 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 285 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 148 = false ∨ valuationOf q 286 = true := by
  have hs : count285 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_two (literal (valuationOf q) (147)) (literal (valuationOf q) (148)) (literal (valuationOf q) (286)) (countLit q [147]) (countLit q [148]) (count285 q) 1 1 (meaning147 q) (meaning148 q) (meaning286 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 148 = false ∨ valuationOf q 286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 148 = false ∨ valuation q 286 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147, 148])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [146]) (countLit q [147, 148]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 286 = false ∨ valuationOf q 288 = true := by
  have hs : count287 q = (countLit q [146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147, 148])
  have hm := merge_right (literal (valuationOf q) (286)) (literal (valuationOf q) (288)) (countLit q [146]) (countLit q [147, 148]) (count287 q) 2 (meaning286 q) (meaning288 q) hs
  change valuationOf q 286 = false ∨ valuationOf q 288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 286 = false ∨ valuation q 288 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147, 148])
  have hm := merge_left (literal (valuationOf q) (146)) (literal (valuationOf q) (287)) (countLit q [146]) (countLit q [147, 148]) (count287 q) 1 (meaning146 q) (meaning287 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 287 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [143, 144, 145]) + (countLit q [146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145]) (l₂ := [146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [143, 144, 145]) (countLit q [146, 147, 148]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 288 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [143, 144, 145]) + (countLit q [146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145]) (l₂ := [146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (288)) (literal (valuationOf q) (290)) (countLit q [143, 144, 145]) (countLit q [146, 147, 148]) (count289 q) 2 (meaning288 q) (meaning290 q) hs
  change valuationOf q 288 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 288 = false ∨ valuation q 290 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [143, 144, 145]) + (countLit q [146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145]) (l₂ := [146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (283)) (literal (valuationOf q) (289)) (countLit q [143, 144, 145]) (countLit q [146, 147, 148]) (count289 q) 1 (meaning283 q) (meaning289 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 289 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 153 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [152]) + (countLit q [153]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153])
  have hm := merge_right (literal (valuationOf q) (153)) (literal (valuationOf q) (295)) (countLit q [152]) (countLit q [153]) (count295 q) 1 (meaning153 q) (meaning295 q) hs
  change valuationOf q 153 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 295 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [152]) + (countLit q [153]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153])
  have hm := merge_left (literal (valuationOf q) (152)) (literal (valuationOf q) (295)) (countLit q [152]) (countLit q [153]) (count295 q) 1 (meaning152 q) (meaning295 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 295 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [152, 153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [152, 153]) (l₂ := [154, 155])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (299)) (countLit q [152, 153]) (countLit q [154, 155]) (count299 q) 1 (meaning295 q) (meaning299 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 299 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [149, 150, 151]) (countLit q [152, 153, 154, 155]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (303)) (countLit q [143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 (meaning289 q) (meaning303 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 303 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 290 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (290)) (literal (valuationOf q) (304)) (countLit q [143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155]) (count303 q) 2 (meaning290 q) (meaning304 q) hs
  change valuationOf q 290 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 290 = false ∨ valuation q 304 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 304 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (304)) (literal (valuationOf q) (306)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 2 (meaning304 q) (meaning306 q) hs
  change valuationOf q 304 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 304 = false ∨ valuation q 306 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (305)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 1 (meaning279 q) (meaning305 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 305 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 303 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_two (literal (valuationOf q) (279)) (literal (valuationOf q) (303)) (literal (valuationOf q) (306)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 1 1 (meaning279 q) (meaning303 q) (meaning306 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 303 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 303 = false ∨ valuation q 306 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 280 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (280)) (literal (valuationOf q) (306)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 2 (meaning280 q) (meaning306 q) hs
  change valuationOf q 280 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 280 = false ∨ valuation q 306 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 306 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (306)) (literal (valuationOf q) (308)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count307 q) 2 (meaning306 q) (meaning308 q) hs
  change valuationOf q 306 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 306 = false ∨ valuation q 308 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (307)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count307 q) 1 (meaning255 q) (meaning307 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 307 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E179.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112179
