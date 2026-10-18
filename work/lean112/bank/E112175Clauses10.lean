import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 272 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [139, 140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [139, 140]) (l₂ := [141, 142])
  have hm := merge_left (literal (valuationOf q) (272)) (literal (valuationOf q) (276)) (countLit q [139, 140]) (countLit q [141, 142]) (count275 q) 2 (meaning272 q) (meaning276 q) hs
  change valuationOf q 272 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 276 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141, 142]) (count277 q) 1 (meaning275 q) (meaning277 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 276 = false ∨ valuationOf q 278 = true := by
  have hs : count277 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (276)) (literal (valuationOf q) (278)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141, 142]) (count277 q) 2 (meaning276 q) (meaning278 q) hs
  change valuationOf q 276 = false ∨ valuationOf q 278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 276 = false ∨ valuation q 278 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (277)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141, 142]) (count277 q) 1 (meaning269 q) (meaning277 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 277 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 275 = false ∨ valuationOf q 278 = true := by
  have hs : count277 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141, 142])
  have hm := merge_two (literal (valuationOf q) (269)) (literal (valuationOf q) (275)) (literal (valuationOf q) (278)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141, 142]) (count277 q) 1 1 (meaning269 q) (meaning275 q) (meaning278 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 275 = false ∨ valuationOf q 278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 275 = false ∨ valuation q 278 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 278 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (278)) (literal (valuationOf q) (280)) (countLit q [130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142]) (count279 q) 2 (meaning278 q) (meaning280 q) hs
  change valuationOf q 278 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 278 = false ∨ valuation q 280 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (279)) (countLit q [130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142]) (count279 q) 1 (meaning265 q) (meaning279 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 279 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (277)) (literal (valuationOf q) (280)) (countLit q [130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142]) (count279 q) 1 1 (meaning265 q) (meaning277 q) (meaning280 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 277 = false ∨ valuation q 280 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_right (literal (valuationOf q) (148)) (literal (valuationOf q) (285)) (countLit q [147]) (countLit q [148]) (count285 q) 1 (meaning148 q) (meaning285 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 285 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_left (literal (valuationOf q) (147)) (literal (valuationOf q) (285)) (countLit q [147]) (countLit q [148]) (count285 q) 1 (meaning147 q) (meaning285 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 285 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147, 148])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [146]) (countLit q [147, 148]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147, 148])
  have hm := merge_left (literal (valuationOf q) (146)) (literal (valuationOf q) (287)) (countLit q [146]) (countLit q [147, 148]) (count287 q) 1 (meaning146 q) (meaning287 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 287 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 285 = false ∨ valuationOf q 288 = true := by
  have hs : count287 q = (countLit q [146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147, 148])
  have hm := merge_two (literal (valuationOf q) (146)) (literal (valuationOf q) (285)) (literal (valuationOf q) (288)) (countLit q [146]) (countLit q [147, 148]) (count287 q) 1 1 (meaning146 q) (meaning285 q) (meaning288 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 285 = false ∨ valuationOf q 288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 285 = false ∨ valuation q 288 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [143, 144, 145]) + (countLit q [146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145]) (l₂ := [146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [143, 144, 145]) (countLit q [146, 147, 148]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 288 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [143, 144, 145]) + (countLit q [146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145]) (l₂ := [146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (288)) (literal (valuationOf q) (290)) (countLit q [143, 144, 145]) (countLit q [146, 147, 148]) (count289 q) 2 (meaning288 q) (meaning290 q) hs
  change valuationOf q 288 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 288 = false ∨ valuation q 290 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150, 151])
  have hm := merge_left (literal (valuationOf q) (149)) (literal (valuationOf q) (293)) (countLit q [149]) (countLit q [150, 151]) (count293 q) 1 (meaning149 q) (meaning293 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 293 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 153 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [152]) + (countLit q [153]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153])
  have hm := merge_right (literal (valuationOf q) (153)) (literal (valuationOf q) (295)) (countLit q [152]) (countLit q [153]) (count295 q) 1 (meaning153 q) (meaning295 q) hs
  change valuationOf q 153 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 295 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [154]) + (countLit q [155]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155])
  have hm := merge_left (literal (valuationOf q) (154)) (literal (valuationOf q) (297)) (countLit q [154]) (countLit q [155]) (count297 q) 1 (meaning154 q) (meaning297 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 297 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [152, 153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [152, 153]) (l₂ := [154, 155])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [152, 153]) (countLit q [154, 155]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [152, 153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [152, 153]) (l₂ := [154, 155])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (299)) (countLit q [152, 153]) (countLit q [154, 155]) (count299 q) 1 (meaning295 q) (meaning299 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 299 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [149, 150, 151]) (countLit q [152, 153, 154, 155]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (301)) (countLit q [149, 150, 151]) (countLit q [152, 153, 154, 155]) (count301 q) 1 (meaning293 q) (meaning301 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 301 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (299)) (literal (valuationOf q) (302)) (countLit q [149, 150, 151]) (countLit q [152, 153, 154, 155]) (count301 q) 1 1 (meaning293 q) (meaning299 q) (meaning302 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 299 = false ∨ valuation q 302 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 302 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (302)) (literal (valuationOf q) (304)) (countLit q [143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155]) (count303 q) 2 (meaning302 q) (meaning304 q) hs
  change valuationOf q 302 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 302 = false ∨ valuation q 304 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (303)) (countLit q [143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 (meaning289 q) (meaning303 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 303 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155])
  have hm := merge_two (literal (valuationOf q) (289)) (literal (valuationOf q) (301)) (literal (valuationOf q) (304)) (countLit q [143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 1 (meaning289 q) (meaning301 q) (meaning304 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 301 = false ∨ valuation q 304 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 290 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (290)) (literal (valuationOf q) (304)) (countLit q [143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155]) (count303 q) 2 (meaning290 q) (meaning304 q) hs
  change valuationOf q 290 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 290 = false ∨ valuation q 304 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 304 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (304)) (literal (valuationOf q) (306)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 2 (meaning304 q) (meaning306 q) hs
  change valuationOf q 304 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 304 = false ∨ valuation q 306 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (305)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 1 (meaning279 q) (meaning305 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 305 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E175.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112175
