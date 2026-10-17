import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (401)) (countLit q [202, 203]) (countLit q [204, 205]) (count401 q) 1 (meaning397 q) (meaning401 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 401 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = false ∨ valuationOf q 402 = true := by
  have hs : count401 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_two (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (literal (valuationOf q) (402)) (countLit q [202, 203]) (countLit q [204, 205]) (count401 q) 1 1 (meaning397 q) (meaning399 q) (meaning402 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = false ∨ valuationOf q 402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = false ∨ valuation q 402 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [198, 199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [198, 199, 200, 201]) (countLit q [202, 203, 204, 205]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 402 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [198, 199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_right (literal (valuationOf q) (402)) (literal (valuationOf q) (404)) (countLit q [198, 199, 200, 201]) (countLit q [202, 203, 204, 205]) (count403 q) 2 (meaning402 q) (meaning404 q) hs
  change valuationOf q 402 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 402 = false ∨ valuation q 404 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [198, 199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (403)) (countLit q [198, 199, 200, 201]) (countLit q [202, 203, 204, 205]) (count403 q) 1 (meaning395 q) (meaning403 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 403 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [198, 199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_two (literal (valuationOf q) (395)) (literal (valuationOf q) (401)) (literal (valuationOf q) (404)) (countLit q [198, 199, 200, 201]) (countLit q [202, 203, 204, 205]) (count403 q) 1 1 (meaning395 q) (meaning401 q) (meaning404 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 401 = false ∨ valuation q 404 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205])
  have hm := merge_right (literal (valuationOf q) (404)) (literal (valuationOf q) (406)) (countLit q [191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) (count405 q) 2 (meaning404 q) (meaning406 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 406 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205])
  have hm := merge_left (literal (valuationOf q) (389)) (literal (valuationOf q) (405)) (countLit q [191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) (count405 q) 1 (meaning389 q) (meaning405 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 405 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205])
  have hm := merge_two (literal (valuationOf q) (389)) (literal (valuationOf q) (403)) (literal (valuationOf q) (406)) (countLit q [191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) (count405 q) 1 1 (meaning389 q) (meaning403 q) (meaning406 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 403 = false ∨ valuation q 406 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 390 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205])
  have hm := merge_left (literal (valuationOf q) (390)) (literal (valuationOf q) (406)) (countLit q [191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) (count405 q) 2 (meaning390 q) (meaning406 q) hs
  change valuationOf q 390 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 390 = false ∨ valuation q 406 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [206]) + (countLit q [207]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207])
  have hm := merge_left (literal (valuationOf q) (206)) (literal (valuationOf q) (407)) (countLit q [206]) (countLit q [207]) (count407 q) 1 (meaning206 q) (meaning407 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 407 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 210 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [208]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [210])
  have hm := merge_right (literal (valuationOf q) (210)) (literal (valuationOf q) (409)) (countLit q [208]) (countLit q [210]) (count409 q) 1 (meaning210 q) (meaning409 q) hs
  change valuationOf q 210 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 409 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [206, 207]) + (countLit q [208, 210]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 210])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [206, 207]) (countLit q [208, 210]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [206, 207]) + (countLit q [208, 210]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 210])
  have hm := merge_left (literal (valuationOf q) (407)) (literal (valuationOf q) (411)) (countLit q [206, 207]) (countLit q [208, 210]) (count411 q) 1 (meaning407 q) (meaning411 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 411 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [211]) + (countLit q [212]) := List.countP_append (p := literal q) (l₁ := [211]) (l₂ := [212])
  have hm := merge_left (literal (valuationOf q) (211)) (literal (valuationOf q) (413)) (countLit q [211]) (countLit q [212]) (count413 q) 1 (meaning211 q) (meaning413 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 413 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [211, 212]) + (countLit q [213, 214]) := List.countP_append (p := literal q) (l₁ := [211, 212]) (l₂ := [213, 214])
  have hm := merge_left (literal (valuationOf q) (413)) (literal (valuationOf q) (417)) (countLit q [211, 212]) (countLit q [213, 214]) (count417 q) 1 (meaning413 q) (meaning417 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 417 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [206, 207, 208, 210]) + (countLit q [211, 212, 213, 214]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208, 210]) (l₂ := [211, 212, 213, 214])
  have hm := merge_right (literal (valuationOf q) (417)) (literal (valuationOf q) (419)) (countLit q [206, 207, 208, 210]) (countLit q [211, 212, 213, 214]) (count419 q) 1 (meaning417 q) (meaning419 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [206, 207, 208, 210]) + (countLit q [211, 212, 213, 214]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208, 210]) (l₂ := [211, 212, 213, 214])
  have hm := merge_left (literal (valuationOf q) (411)) (literal (valuationOf q) (419)) (countLit q [206, 207, 208, 210]) (countLit q [211, 212, 213, 214]) (count419 q) 1 (meaning411 q) (meaning419 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 419 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [215]) + (countLit q [216]) := List.countP_append (p := literal q) (l₁ := [215]) (l₂ := [216])
  have hm := merge_left (literal (valuationOf q) (215)) (literal (valuationOf q) (421)) (countLit q [215]) (countLit q [216]) (count421 q) 1 (meaning215 q) (meaning421 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 421 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_right (literal (valuationOf q) (218)) (literal (valuationOf q) (423)) (countLit q [217]) (countLit q [218]) (count423 q) 1 (meaning218 q) (meaning423 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 423 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (423)) (countLit q [217]) (countLit q [218]) (count423 q) 1 (meaning217 q) (meaning423 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 423 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [215, 216]) + (countLit q [217, 218]) := List.countP_append (p := literal q) (l₁ := [215, 216]) (l₂ := [217, 218])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [215, 216]) (countLit q [217, 218]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [215, 216]) + (countLit q [217, 218]) := List.countP_append (p := literal q) (l₁ := [215, 216]) (l₂ := [217, 218])
  have hm := merge_left (literal (valuationOf q) (421)) (literal (valuationOf q) (425)) (countLit q [215, 216]) (countLit q [217, 218]) (count425 q) 1 (meaning421 q) (meaning425 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 425 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [219]) + (countLit q [220]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220])
  have hm := merge_right (literal (valuationOf q) (220)) (literal (valuationOf q) (427)) (countLit q [219]) (countLit q [220]) (count427 q) 1 (meaning220 q) (meaning427 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 427 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [219, 220]) + (countLit q [221, 222]) := List.countP_append (p := literal q) (l₁ := [219, 220]) (l₂ := [221, 222])
  have hm := merge_left (literal (valuationOf q) (427)) (literal (valuationOf q) (431)) (countLit q [219, 220]) (countLit q [221, 222]) (count431 q) 1 (meaning427 q) (meaning431 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 431 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [215, 216, 217, 218]) + (countLit q [219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [215, 216, 217, 218]) (l₂ := [219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (431)) (literal (valuationOf q) (433)) (countLit q [215, 216, 217, 218]) (countLit q [219, 220, 221, 222]) (count433 q) 1 (meaning431 q) (meaning433 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 433 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [215, 216, 217, 218]) + (countLit q [219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [215, 216, 217, 218]) (l₂ := [219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (433)) (countLit q [215, 216, 217, 218]) (countLit q [219, 220, 221, 222]) (count433 q) 1 (meaning425 q) (meaning433 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 433 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [206, 207, 208, 210, 211, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208, 210, 211, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (433)) (literal (valuationOf q) (435)) (countLit q [206, 207, 208, 210, 211, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 (meaning433 q) (meaning435 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 435 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [206, 207, 208, 210, 211, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208, 210, 211, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (435)) (countLit q [206, 207, 208, 210, 211, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 (meaning419 q) (meaning435 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 435 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [206, 207, 208, 210, 211, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208, 210, 211, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (419)) (literal (valuationOf q) (433)) (literal (valuationOf q) (436)) (countLit q [206, 207, 208, 210, 211, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 1 (meaning419 q) (meaning433 q) (meaning436 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 433 = false ∨ valuation q 436 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E256.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112256
