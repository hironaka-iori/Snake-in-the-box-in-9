import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (389)) (countLit q [193, 194, 195]) (countLit q [196, 197, 198, 199]) (count389 q) 1 (meaning381 q) (meaning389 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 389 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 387 = false ∨ valuationOf q 390 = true := by
  have hs : count389 q = (countLit q [193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_two (literal (valuationOf q) (381)) (literal (valuationOf q) (387)) (literal (valuationOf q) (390)) (countLit q [193, 194, 195]) (countLit q [196, 197, 198, 199]) (count389 q) 1 1 (meaning381 q) (meaning387 q) (meaning390 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 387 = false ∨ valuationOf q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 387 = false ∨ valuation q 390 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201, 202])
  have hm := merge_left (literal (valuationOf q) (200)) (literal (valuationOf q) (393)) (countLit q [200]) (countLit q [201, 202]) (count393 q) 1 (meaning200 q) (meaning393 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 393 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (393)) (literal (valuationOf q) (401)) (countLit q [200, 201, 202]) (countLit q [203, 204, 205, 206]) (count401 q) 1 (meaning393 q) (meaning401 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 401 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (389)) (literal (valuationOf q) (403)) (countLit q [193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 (meaning389 q) (meaning403 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 403 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206])
  have hm := merge_two (literal (valuationOf q) (389)) (literal (valuationOf q) (401)) (literal (valuationOf q) (404)) (countLit q [193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 1 (meaning389 q) (meaning401 q) (meaning404 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 401 = false ∨ valuation q 404 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 390 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (390)) (literal (valuationOf q) (404)) (countLit q [193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206]) (count403 q) 2 (meaning390 q) (meaning404 q) hs
  change valuationOf q 390 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 390 = false ∨ valuation q 404 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (405)) (countLit q [208]) (countLit q [209]) (count405 q) 1 (meaning209 q) (meaning405 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 405 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208, 209])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [207]) (countLit q [208, 209]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_left (literal (valuationOf q) (212)) (literal (valuationOf q) (411)) (countLit q [212]) (countLit q [213]) (count411 q) 1 (meaning212 q) (meaning411 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 411 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [210, 211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [210, 211]) (l₂ := [212, 213])
  have hm := merge_right (literal (valuationOf q) (411)) (literal (valuationOf q) (413)) (countLit q [210, 211]) (countLit q [212, 213]) (count413 q) 1 (meaning411 q) (meaning413 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 413 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [207, 208, 209]) + (countLit q [210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209]) (l₂ := [210, 211, 212, 213])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [207, 208, 209]) (countLit q [210, 211, 212, 213]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [207, 208, 209]) + (countLit q [210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209]) (l₂ := [210, 211, 212, 213])
  have hm := merge_left (literal (valuationOf q) (407)) (literal (valuationOf q) (415)) (countLit q [207, 208, 209]) (countLit q [210, 211, 212, 213]) (count415 q) 1 (meaning407 q) (meaning415 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 415 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 413 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [207, 208, 209]) + (countLit q [210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209]) (l₂ := [210, 211, 212, 213])
  have hm := merge_two (literal (valuationOf q) (407)) (literal (valuationOf q) (413)) (literal (valuationOf q) (416)) (countLit q [207, 208, 209]) (countLit q [210, 211, 212, 213]) (count415 q) 1 1 (meaning407 q) (meaning413 q) (meaning416 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 413 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 413 = false ∨ valuation q 416 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 216 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [215]) + (countLit q [216]) := List.countP_append (p := literal q) (l₁ := [215]) (l₂ := [216])
  have hm := merge_right (literal (valuationOf q) (216)) (literal (valuationOf q) (417)) (countLit q [215]) (countLit q [216]) (count417 q) 1 (meaning216 q) (meaning417 q) hs
  change valuationOf q 216 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 417 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [214]) + (countLit q [215, 216]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215, 216])
  have hm := merge_right (literal (valuationOf q) (417)) (literal (valuationOf q) (419)) (countLit q [214]) (countLit q [215, 216]) (count419 q) 1 (meaning417 q) (meaning419 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_right (literal (valuationOf q) (218)) (literal (valuationOf q) (421)) (countLit q [217]) (countLit q [218]) (count421 q) 1 (meaning218 q) (meaning421 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 421 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 218 = false ∨ valuationOf q 422 = true := by
  have hs : count421 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_two (literal (valuationOf q) (217)) (literal (valuationOf q) (218)) (literal (valuationOf q) (422)) (countLit q [217]) (countLit q [218]) (count421 q) 1 1 (meaning217 q) (meaning218 q) (meaning422 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 218 = false ∨ valuationOf q 422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 218 = false ∨ valuation q 422 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [217, 218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [217, 218]) (l₂ := [219, 220])
  have hm := merge_left (literal (valuationOf q) (421)) (literal (valuationOf q) (425)) (countLit q [217, 218]) (countLit q [219, 220]) (count425 q) 1 (meaning421 q) (meaning425 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 425 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 422 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [217, 218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [217, 218]) (l₂ := [219, 220])
  have hm := merge_left (literal (valuationOf q) (422)) (literal (valuationOf q) (426)) (countLit q [217, 218]) (countLit q [219, 220]) (count425 q) 2 (meaning422 q) (meaning426 q) hs
  change valuationOf q 422 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 422 = false ∨ valuation q 426 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [214, 215, 216]) + (countLit q [217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216]) (l₂ := [217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [214, 215, 216]) (countLit q [217, 218, 219, 220]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 426 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [214, 215, 216]) + (countLit q [217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216]) (l₂ := [217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (426)) (literal (valuationOf q) (428)) (countLit q [214, 215, 216]) (countLit q [217, 218, 219, 220]) (count427 q) 2 (meaning426 q) (meaning428 q) hs
  change valuationOf q 426 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 426 = false ∨ valuation q 428 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [214, 215, 216]) + (countLit q [217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216]) (l₂ := [217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (427)) (countLit q [214, 215, 216]) (countLit q [217, 218, 219, 220]) (count427 q) 1 (meaning419 q) (meaning427 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 427 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 428 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (428)) (literal (valuationOf q) (430)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220]) (count429 q) 2 (meaning428 q) (meaning430 q) hs
  change valuationOf q 428 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 428 = false ∨ valuation q 430 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (415)) (literal (valuationOf q) (429)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220]) (count429 q) 1 (meaning415 q) (meaning429 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 429 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 416 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (416)) (literal (valuationOf q) (430)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220]) (count429 q) 2 (meaning416 q) (meaning430 q) hs
  change valuationOf q 416 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 416 = false ∨ valuation q 430 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 430 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (430)) (literal (valuationOf q) (432)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 2 (meaning430 q) (meaning432 q) hs
  change valuationOf q 430 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 430 = false ∨ valuation q 432 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (431)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 1 (meaning403 q) (meaning431 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 431 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (404)) (literal (valuationOf q) (432)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 2 (meaning404 q) (meaning432 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 432 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E107.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112107
