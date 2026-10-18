import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139, 140])
  have hm := merge_left (literal (valuationOf q) (138)) (literal (valuationOf q) (273)) (countLit q [138]) (countLit q [139, 140]) (count273 q) 1 (meaning138 q) (meaning273 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 273 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [135, 136, 137]) + (countLit q [138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137]) (l₂ := [138, 139, 140])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [135, 136, 137]) (countLit q [138, 139, 140]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [135, 136, 137]) + (countLit q [138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137]) (l₂ := [138, 139, 140])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (275)) (countLit q [135, 136, 137]) (countLit q [138, 139, 140]) (count275 q) 1 (meaning269 q) (meaning275 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 275 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [135, 136, 137]) + (countLit q [138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137]) (l₂ := [138, 139, 140])
  have hm := merge_two (literal (valuationOf q) (269)) (literal (valuationOf q) (273)) (literal (valuationOf q) (276)) (countLit q [135, 136, 137]) (countLit q [138, 139, 140]) (count275 q) 1 1 (meaning269 q) (meaning273 q) (meaning276 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 273 = false ∨ valuation q 276 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [142]) + (countLit q [143]) := List.countP_append (p := literal q) (l₁ := [142]) (l₂ := [143])
  have hm := merge_right (literal (valuationOf q) (143)) (literal (valuationOf q) (277)) (countLit q [142]) (countLit q [143]) (count277 q) 1 (meaning143 q) (meaning277 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 277 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142, 143])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [141]) (countLit q [142, 143]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142, 143])
  have hm := merge_left (literal (valuationOf q) (141)) (literal (valuationOf q) (279)) (countLit q [141]) (countLit q [142, 143]) (count279 q) 1 (meaning141 q) (meaning279 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 279 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [144]) + (countLit q [145]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145])
  have hm := merge_left (literal (valuationOf q) (144)) (literal (valuationOf q) (281)) (countLit q [144]) (countLit q [145]) (count281 q) 1 (meaning144 q) (meaning281 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 281 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (285)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 1 (meaning281 q) (meaning285 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 285 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (287)) (countLit q [141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 (meaning279 q) (meaning287 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 287 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 285 = false ∨ valuationOf q 288 = true := by
  have hs : count287 q = (countLit q [141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_two (literal (valuationOf q) (279)) (literal (valuationOf q) (285)) (literal (valuationOf q) (288)) (countLit q [141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 1 (meaning279 q) (meaning285 q) (meaning288 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 285 = false ∨ valuationOf q 288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 285 = false ∨ valuation q 288 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 288 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (288)) (literal (valuationOf q) (290)) (countLit q [135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147]) (count289 q) 2 (meaning288 q) (meaning290 q) hs
  change valuationOf q 288 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 288 = false ∨ valuation q 290 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (289)) (countLit q [135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147]) (count289 q) 1 (meaning275 q) (meaning289 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 289 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 276 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (276)) (literal (valuationOf q) (290)) (countLit q [135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147]) (count289 q) 2 (meaning276 q) (meaning290 q) hs
  change valuationOf q 276 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 276 = false ∨ valuation q 290 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_right (literal (valuationOf q) (150)) (literal (valuationOf q) (291)) (countLit q [149]) (countLit q [150]) (count291 q) 1 (meaning150 q) (meaning291 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 291 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_left (literal (valuationOf q) (149)) (literal (valuationOf q) (291)) (countLit q [149]) (countLit q [150]) (count291 q) 1 (meaning149 q) (meaning291 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 291 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 150 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_two (literal (valuationOf q) (149)) (literal (valuationOf q) (150)) (literal (valuationOf q) (292)) (countLit q [149]) (countLit q [150]) (count291 q) 1 1 (meaning149 q) (meaning150 q) (meaning292 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 150 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 150 = false ∨ valuation q 292 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149, 150])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [148]) (countLit q [149, 150]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 292 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149, 150])
  have hm := merge_right (literal (valuationOf q) (292)) (literal (valuationOf q) (294)) (countLit q [148]) (countLit q [149, 150]) (count293 q) 2 (meaning292 q) (meaning294 q) hs
  change valuationOf q 292 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 292 = false ∨ valuation q 294 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_right (literal (valuationOf q) (152)) (literal (valuationOf q) (295)) (countLit q [151]) (countLit q [152]) (count295 q) 1 (meaning152 q) (meaning295 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 295 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (299)) (countLit q [151, 152]) (countLit q [153, 154]) (count299 q) 1 (meaning295 q) (meaning299 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 299 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [148, 149, 150]) (countLit q [151, 152, 153, 154]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (301)) (countLit q [148, 149, 150]) (countLit q [151, 152, 153, 154]) (count301 q) 1 (meaning293 q) (meaning301 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 301 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (299)) (literal (valuationOf q) (302)) (countLit q [148, 149, 150]) (countLit q [151, 152, 153, 154]) (count301 q) 1 1 (meaning293 q) (meaning299 q) (meaning302 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 299 = false ∨ valuation q 302 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_left (literal (valuationOf q) (294)) (literal (valuationOf q) (302)) (countLit q [148, 149, 150]) (countLit q [151, 152, 153, 154]) (count301 q) 2 (meaning294 q) (meaning302 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 302 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_right (literal (valuationOf q) (158)) (literal (valuationOf q) (303)) (countLit q [157]) (countLit q [158]) (count303 q) 1 (meaning158 q) (meaning303 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 303 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_left (literal (valuationOf q) (157)) (literal (valuationOf q) (303)) (countLit q [157]) (countLit q [158]) (count303 q) 1 (meaning157 q) (meaning303 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 303 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 158 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_two (literal (valuationOf q) (157)) (literal (valuationOf q) (158)) (literal (valuationOf q) (304)) (countLit q [157]) (countLit q [158]) (count303 q) 1 1 (meaning157 q) (meaning158 q) (meaning304 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 158 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 158 = false ∨ valuation q 304 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [155]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [157, 158])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [155]) (countLit q [157, 158]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 304 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [155]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [157, 158])
  have hm := merge_right (literal (valuationOf q) (304)) (literal (valuationOf q) (306)) (countLit q [155]) (countLit q [157, 158]) (count305 q) 2 (meaning304 q) (meaning306 q) hs
  change valuationOf q 304 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 304 = false ∨ valuation q 306 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_right (literal (valuationOf q) (160)) (literal (valuationOf q) (307)) (countLit q [159]) (countLit q [160]) (count307 q) 1 (meaning160 q) (meaning307 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 307 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E185.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112185
