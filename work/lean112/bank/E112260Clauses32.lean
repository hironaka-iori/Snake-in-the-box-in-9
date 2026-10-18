import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 201 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_two (literal (valuationOf q) (200)) (literal (valuationOf q) (201)) (literal (valuationOf q) (394)) (countLit q [200]) (countLit q [201]) (count393 q) 1 1 (meaning200 q) (meaning201 q) (meaning394 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 201 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 201 = false ∨ valuation q 394 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [198, 199]) (countLit q [200, 201]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 394 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_right (literal (valuationOf q) (394)) (literal (valuationOf q) (396)) (countLit q [198, 199]) (countLit q [200, 201]) (count395 q) 2 (meaning394 q) (meaning396 q) hs
  change valuationOf q 394 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 394 = false ∨ valuation q 396 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (395)) (countLit q [198, 199]) (countLit q [200, 201]) (count395 q) 1 (meaning391 q) (meaning395 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 395 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_two (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (literal (valuationOf q) (396)) (countLit q [198, 199]) (countLit q [200, 201]) (count395 q) 1 1 (meaning391 q) (meaning393 q) (meaning396 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = false ∨ valuation q 396 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [202]) + (countLit q [203]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203])
  have hm := merge_right (literal (valuationOf q) (203)) (literal (valuationOf q) (397)) (countLit q [202]) (countLit q [203]) (count397 q) 1 (meaning203 q) (meaning397 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 397 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (401)) (countLit q [202, 203]) (countLit q [204, 205]) (count401 q) 1 (meaning397 q) (meaning401 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 401 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [198, 199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [198, 199, 200, 201]) (countLit q [202, 203, 204, 205]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [198, 199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (403)) (countLit q [198, 199, 200, 201]) (countLit q [202, 203, 204, 205]) (count403 q) 1 (meaning395 q) (meaning403 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 403 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [198, 199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_two (literal (valuationOf q) (395)) (literal (valuationOf q) (401)) (literal (valuationOf q) (404)) (countLit q [198, 199, 200, 201]) (countLit q [202, 203, 204, 205]) (count403 q) 1 1 (meaning395 q) (meaning401 q) (meaning404 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 401 = false ∨ valuation q 404 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 396 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [198, 199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_left (literal (valuationOf q) (396)) (literal (valuationOf q) (404)) (countLit q [198, 199, 200, 201]) (countLit q [202, 203, 204, 205]) (count403 q) 2 (meaning396 q) (meaning404 q) hs
  change valuationOf q 396 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 396 = false ∨ valuation q 404 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205])
  have hm := merge_right (literal (valuationOf q) (404)) (literal (valuationOf q) (406)) (countLit q [191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) (count405 q) 2 (meaning404 q) (meaning406 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 406 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205])
  have hm := merge_left (literal (valuationOf q) (389)) (literal (valuationOf q) (405)) (countLit q [191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) (count405 q) 1 (meaning389 q) (meaning405 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 405 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205])
  have hm := merge_two (literal (valuationOf q) (389)) (literal (valuationOf q) (403)) (literal (valuationOf q) (406)) (countLit q [191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) (count405 q) 1 1 (meaning389 q) (meaning403 q) (meaning406 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 403 = false ∨ valuation q 406 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 390 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205])
  have hm := merge_left (literal (valuationOf q) (390)) (literal (valuationOf q) (406)) (countLit q [191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205]) (count405 q) 2 (meaning390 q) (meaning406 q) hs
  change valuationOf q 390 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 390 = false ∨ valuation q 406 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [206]) + (countLit q [207]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207])
  have hm := merge_left (literal (valuationOf q) (206)) (literal (valuationOf q) (407)) (countLit q [206]) (countLit q [207]) (count407 q) 1 (meaning206 q) (meaning407 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 407 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (409)) (countLit q [208]) (countLit q [209]) (count409 q) 1 (meaning209 q) (meaning409 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 409 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_left (literal (valuationOf q) (208)) (literal (valuationOf q) (409)) (countLit q [208]) (countLit q [209]) (count409 q) 1 (meaning208 q) (meaning409 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 409 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [206, 207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 209])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [206, 207]) (countLit q [208, 209]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [206, 207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 209])
  have hm := merge_left (literal (valuationOf q) (407)) (literal (valuationOf q) (411)) (countLit q [206, 207]) (countLit q [208, 209]) (count411 q) 1 (meaning407 q) (meaning411 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 411 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [210]) + (countLit q [212]) := List.countP_append (p := literal q) (l₁ := [210]) (l₂ := [212])
  have hm := merge_right (literal (valuationOf q) (212)) (literal (valuationOf q) (413)) (countLit q [210]) (countLit q [212]) (count413 q) 1 (meaning212 q) (meaning413 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 413 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [213]) + (countLit q [214]) := List.countP_append (p := literal q) (l₁ := [213]) (l₂ := [214])
  have hm := merge_left (literal (valuationOf q) (213)) (literal (valuationOf q) (415)) (countLit q [213]) (countLit q [214]) (count415 q) 1 (meaning213 q) (meaning415 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 415 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [210, 212]) + (countLit q [213, 214]) := List.countP_append (p := literal q) (l₁ := [210, 212]) (l₂ := [213, 214])
  have hm := merge_right (literal (valuationOf q) (415)) (literal (valuationOf q) (417)) (countLit q [210, 212]) (countLit q [213, 214]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [210, 212]) + (countLit q [213, 214]) := List.countP_append (p := literal q) (l₁ := [210, 212]) (l₂ := [213, 214])
  have hm := merge_left (literal (valuationOf q) (413)) (literal (valuationOf q) (417)) (countLit q [210, 212]) (countLit q [213, 214]) (count417 q) 1 (meaning413 q) (meaning417 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 417 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [206, 207, 208, 209]) + (countLit q [210, 212, 213, 214]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208, 209]) (l₂ := [210, 212, 213, 214])
  have hm := merge_right (literal (valuationOf q) (417)) (literal (valuationOf q) (419)) (countLit q [206, 207, 208, 209]) (countLit q [210, 212, 213, 214]) (count419 q) 1 (meaning417 q) (meaning419 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [206, 207, 208, 209]) + (countLit q [210, 212, 213, 214]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208, 209]) (l₂ := [210, 212, 213, 214])
  have hm := merge_left (literal (valuationOf q) (411)) (literal (valuationOf q) (419)) (countLit q [206, 207, 208, 209]) (countLit q [210, 212, 213, 214]) (count419 q) 1 (meaning411 q) (meaning419 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 419 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 216 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [215]) + (countLit q [216]) := List.countP_append (p := literal q) (l₁ := [215]) (l₂ := [216])
  have hm := merge_right (literal (valuationOf q) (216)) (literal (valuationOf q) (421)) (countLit q [215]) (countLit q [216]) (count421 q) 1 (meaning216 q) (meaning421 q) hs
  change valuationOf q 216 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 421 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (423)) (countLit q [217]) (countLit q [218]) (count423 q) 1 (meaning217 q) (meaning423 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 423 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [215, 216]) + (countLit q [217, 218]) := List.countP_append (p := literal q) (l₁ := [215, 216]) (l₂ := [217, 218])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [215, 216]) (countLit q [217, 218]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [215, 216]) + (countLit q [217, 218]) := List.countP_append (p := literal q) (l₁ := [215, 216]) (l₂ := [217, 218])
  have hm := merge_left (literal (valuationOf q) (421)) (literal (valuationOf q) (425)) (countLit q [215, 216]) (countLit q [217, 218]) (count425 q) 1 (meaning421 q) (meaning425 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 425 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [215, 216]) + (countLit q [217, 218]) := List.countP_append (p := literal q) (l₁ := [215, 216]) (l₂ := [217, 218])
  have hm := merge_two (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (literal (valuationOf q) (426)) (countLit q [215, 216]) (countLit q [217, 218]) (count425 q) 1 1 (meaning421 q) (meaning423 q) (meaning426 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = false ∨ valuation q 426 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E260.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112260
