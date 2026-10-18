import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_right (literal (valuationOf q) (201)) (literal (valuationOf q) (389)) (countLit q [200]) (countLit q [201]) (count389 q) 1 (meaning201 q) (meaning389 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 389 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (391)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 1 (meaning387 q) (meaning391 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 391 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [194, 195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [194, 195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [194, 195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_left (literal (valuationOf q) (385)) (literal (valuationOf q) (393)) (countLit q [194, 195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 1 (meaning385 q) (meaning393 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 393 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (395)) (countLit q [187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) (count395 q) 1 (meaning379 q) (meaning395 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 395 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [202]) + (countLit q [203]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203])
  have hm := merge_right (literal (valuationOf q) (203)) (literal (valuationOf q) (397)) (countLit q [202]) (countLit q [203]) (count397 q) 1 (meaning203 q) (meaning397 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 397 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [204]) + (countLit q [205]) := List.countP_append (p := literal q) (l₁ := [204]) (l₂ := [205])
  have hm := merge_right (literal (valuationOf q) (205)) (literal (valuationOf q) (399)) (countLit q [204]) (countLit q [205]) (count399 q) 1 (meaning205 q) (meaning399 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 399 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [202, 203]) (countLit q [204, 205]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (401)) (countLit q [202, 203]) (countLit q [204, 205]) (count401 q) 1 (meaning397 q) (meaning401 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 401 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (405)) (countLit q [208]) (countLit q [209]) (count405 q) 1 (meaning209 q) (meaning405 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 405 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [206, 207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 209])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [206, 207]) (countLit q [208, 209]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [202, 203, 204, 205]) + (countLit q [206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205]) (l₂ := [206, 207, 208, 209])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [202, 203, 204, 205]) (countLit q [206, 207, 208, 209]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [202, 203, 204, 205]) + (countLit q [206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205]) (l₂ := [206, 207, 208, 209])
  have hm := merge_left (literal (valuationOf q) (401)) (literal (valuationOf q) (409)) (countLit q [202, 203, 204, 205]) (countLit q [206, 207, 208, 209]) (count409 q) 1 (meaning401 q) (meaning409 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 409 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [210]) + (countLit q [211]) := List.countP_append (p := literal q) (l₁ := [210]) (l₂ := [211])
  have hm := merge_right (literal (valuationOf q) (211)) (literal (valuationOf q) (411)) (countLit q [210]) (countLit q [211]) (count411 q) 1 (meaning211 q) (meaning411 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 411 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 210 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [210]) + (countLit q [211]) := List.countP_append (p := literal q) (l₁ := [210]) (l₂ := [211])
  have hm := merge_left (literal (valuationOf q) (210)) (literal (valuationOf q) (411)) (countLit q [210]) (countLit q [211]) (count411 q) 1 (meaning210 q) (meaning411 q) hs
  change valuationOf q 210 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 411 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [210, 211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [210, 211]) (l₂ := [212, 213])
  have hm := merge_left (literal (valuationOf q) (411)) (literal (valuationOf q) (415)) (countLit q [210, 211]) (countLit q [212, 213]) (count415 q) 1 (meaning411 q) (meaning415 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 415 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 214 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_left (literal (valuationOf q) (214)) (literal (valuationOf q) (417)) (countLit q [214]) (countLit q [215]) (count417 q) 1 (meaning214 q) (meaning417 q) hs
  change valuationOf q 214 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 417 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [216]) + (countLit q [217]) := List.countP_append (p := literal q) (l₁ := [216]) (l₂ := [217])
  have hm := merge_right (literal (valuationOf q) (217)) (literal (valuationOf q) (419)) (countLit q [216]) (countLit q [217]) (count419 q) 1 (meaning217 q) (meaning419 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 419 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_right (literal (valuationOf q) (419)) (literal (valuationOf q) (421)) (countLit q [214, 215]) (countLit q [216, 217]) (count421 q) 1 (meaning419 q) (meaning421 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 421 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (421)) (countLit q [214, 215]) (countLit q [216, 217]) (count421 q) 1 (meaning417 q) (meaning421 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 421 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [210, 211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (countLit q [210, 211, 212, 213]) (countLit q [214, 215, 216, 217]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [210, 211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (415)) (literal (valuationOf q) (423)) (countLit q [210, 211, 212, 213]) (countLit q [214, 215, 216, 217]) (count423 q) 1 (meaning415 q) (meaning423 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 423 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 421 = false ∨ valuationOf q 424 = true := by
  have hs : count423 q = (countLit q [210, 211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_two (literal (valuationOf q) (415)) (literal (valuationOf q) (421)) (literal (valuationOf q) (424)) (countLit q [210, 211, 212, 213]) (countLit q [214, 215, 216, 217]) (count423 q) 1 1 (meaning415 q) (meaning421 q) (meaning424 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 421 = false ∨ valuationOf q 424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 421 = false ∨ valuation q 424 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 424 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (424)) (literal (valuationOf q) (426)) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) (count425 q) 2 (meaning424 q) (meaning426 q) hs
  change valuationOf q 424 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 424 = false ∨ valuation q 426 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (409)) (literal (valuationOf q) (425)) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) (count425 q) 1 (meaning409 q) (meaning425 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 425 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 426 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (426)) (literal (valuationOf q) (428)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (count427 q) 2 (meaning426 q) (meaning428 q) hs
  change valuationOf q 426 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 426 = false ∨ valuation q 428 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (427)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (count427 q) 1 (meaning395 q) (meaning427 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 427 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_two (literal (valuationOf q) (395)) (literal (valuationOf q) (425)) (literal (valuationOf q) (428)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (count427 q) 1 1 (meaning395 q) (meaning425 q) (meaning428 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 425 = false ∨ valuation q 428 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E020.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112020
