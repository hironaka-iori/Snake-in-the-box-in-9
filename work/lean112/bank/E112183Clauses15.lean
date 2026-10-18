import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [214]) + (countLit q [215, 216]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215, 216])
  have hm := merge_right (literal (valuationOf q) (417)) (literal (valuationOf q) (419)) (countLit q [214]) (countLit q [215, 216]) (count419 q) 1 (meaning417 q) (meaning419 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (421)) (countLit q [217]) (countLit q [218]) (count421 q) 1 (meaning217 q) (meaning421 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 421 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [219]) + (countLit q [220]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220])
  have hm := merge_left (literal (valuationOf q) (219)) (literal (valuationOf q) (423)) (countLit q [219]) (countLit q [220]) (count423 q) 1 (meaning219 q) (meaning423 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 423 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [217, 218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [217, 218]) (l₂ := [219, 220])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [217, 218]) (countLit q [219, 220]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [217, 218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [217, 218]) (l₂ := [219, 220])
  have hm := merge_left (literal (valuationOf q) (421)) (literal (valuationOf q) (425)) (countLit q [217, 218]) (countLit q [219, 220]) (count425 q) 1 (meaning421 q) (meaning425 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 425 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [214, 215, 216]) + (countLit q [217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216]) (l₂ := [217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [214, 215, 216]) (countLit q [217, 218, 219, 220]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [214, 215, 216]) + (countLit q [217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216]) (l₂ := [217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (427)) (countLit q [214, 215, 216]) (countLit q [217, 218, 219, 220]) (count427 q) 1 (meaning419 q) (meaning427 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 427 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (415)) (literal (valuationOf q) (429)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220]) (count429 q) 1 (meaning415 q) (meaning429 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 429 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (431)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 1 (meaning403 q) (meaning431 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 431 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_two (literal (valuationOf q) (403)) (literal (valuationOf q) (429)) (literal (valuationOf q) (432)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 1 1 (meaning403 q) (meaning429 q) (meaning432 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 429 = false ∨ valuation q 432 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (404)) (literal (valuationOf q) (432)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 2 (meaning404 q) (meaning432 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 432 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (431)) (literal (valuationOf q) (433)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 1 (meaning431 q) (meaning433 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 433 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 432 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (432)) (literal (valuationOf q) (434)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 2 (meaning432 q) (meaning434 q) hs
  change valuationOf q 432 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 432 = false ∨ valuation q 434 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (433)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 1 (meaning377 q) (meaning433 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 433 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_two (literal (valuationOf q) (377)) (literal (valuationOf q) (431)) (literal (valuationOf q) (434)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 1 1 (meaning377 q) (meaning431 q) (meaning434 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 431 = false ∨ valuation q 434 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (378)) (literal (valuationOf q) (434)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 2 (meaning378 q) (meaning434 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 434 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 434 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (434)) (literal (valuationOf q) (436)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count435 q) 2 (meaning434 q) (meaning436 q) hs
  change valuationOf q 434 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 434 = false ∨ valuation q 436 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_two (literal (valuationOf q) (325)) (literal (valuationOf q) (433)) (literal (valuationOf q) (436)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count435 q) 1 1 (meaning325 q) (meaning433 q) (meaning436 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 433 = false ∨ valuation q 436 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 326 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (326)) (literal (valuationOf q) (436)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count435 q) 2 (meaning326 q) (meaning436 q) hs
  change valuationOf q 326 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 326 = false ∨ valuation q 436 = true := counterClause501 (baseVal q)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 436 = false := by
  rw [value436]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count435 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause503 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-3]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1333)) (countLit q [-3]) (countLit q [-7]) (count1333 q) 1 (meaningNeg7 q) (meaning1333 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1333 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-3]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1333)) (countLit q [-3]) (countLit q [-7]) (count1333 q) 1 (meaningNeg3 q) (meaning1333 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1333 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1334 = true := by
  have hs : count1333 q = (countLit q [-3]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1334)) (countLit q [-3]) (countLit q [-7]) (count1333 q) 1 1 (meaningNeg3 q) (meaningNeg7 q) (meaning1334 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 7 = true ∨ valuation q 1334 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1335 = true := by
  have hs : count1335 q = (countLit q [-2]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -7])
  have hm := merge_right (literal (valuationOf q) (1333)) (literal (valuationOf q) (1335)) (countLit q [-2]) (countLit q [-3, -7]) (count1335 q) 1 (meaning1333 q) (meaning1335 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1335 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1336 = true := by
  have hs : count1335 q = (countLit q [-2]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -7])
  have hm := merge_right (literal (valuationOf q) (1334)) (literal (valuationOf q) (1336)) (countLit q [-2]) (countLit q [-3, -7]) (count1335 q) 2 (meaning1334 q) (meaning1336 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1336 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1335 = true := by
  have hs : count1335 q = (countLit q [-2]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -7])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1335)) (countLit q [-2]) (countLit q [-3, -7]) (count1335 q) 1 (meaningNeg2 q) (meaning1335 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1335 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1333 = false ∨ valuationOf q 1336 = true := by
  have hs : count1335 q = (countLit q [-2]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1333)) (literal (valuationOf q) (1336)) (countLit q [-2]) (countLit q [-3, -7]) (count1335 q) 1 1 (meaningNeg2 q) (meaning1333 q) (meaning1336 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1333 = false ∨ valuation q 1336 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1334 = false ∨ valuationOf q 1337 = true := by
  have hs : count1335 q = (countLit q [-2]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1334)) (literal (valuationOf q) (1337)) (countLit q [-2]) (countLit q [-3, -7]) (count1335 q) 1 2 (meaningNeg2 q) (meaning1334 q) (meaning1337 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1334 = false ∨ valuation q 1337 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-10]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1338)) (countLit q [-10]) (countLit q [-13]) (count1338 q) 1 (meaningNeg13 q) (meaning1338 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1338 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-10]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1338)) (countLit q [-10]) (countLit q [-13]) (count1338 q) 1 (meaningNeg10 q) (meaning1338 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1338 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E183.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112183
