import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (395)) (countLit q [190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202]) (count395 q) 1 (meaning381 q) (meaning395 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 395 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 382 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (382)) (literal (valuationOf q) (396)) (countLit q [190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202]) (count395 q) 2 (meaning382 q) (meaning396 q) hs
  change valuationOf q 382 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 382 = false ∨ valuation q 396 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [211]) + (countLit q [212]) := List.countP_append (p := literal q) (l₁ := [211]) (l₂ := [212])
  have hm := merge_right (literal (valuationOf q) (212)) (literal (valuationOf q) (409)) (countLit q [211]) (countLit q [212]) (count409 q) 1 (meaning212 q) (meaning409 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 409 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [210]) + (countLit q [211, 212]) := List.countP_append (p := literal q) (l₁ := [210]) (l₂ := [211, 212])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [210]) (countLit q [211, 212]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [213]) + (countLit q [214]) := List.countP_append (p := literal q) (l₁ := [213]) (l₂ := [214])
  have hm := merge_left (literal (valuationOf q) (213)) (literal (valuationOf q) (413)) (countLit q [213]) (countLit q [214]) (count413 q) 1 (meaning213 q) (meaning413 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 413 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [215]) + (countLit q [216]) := List.countP_append (p := literal q) (l₁ := [215]) (l₂ := [216])
  have hm := merge_left (literal (valuationOf q) (215)) (literal (valuationOf q) (415)) (countLit q [215]) (countLit q [216]) (count415 q) 1 (meaning215 q) (meaning415 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 415 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [213, 214]) + (countLit q [215, 216]) := List.countP_append (p := literal q) (l₁ := [213, 214]) (l₂ := [215, 216])
  have hm := merge_right (literal (valuationOf q) (415)) (literal (valuationOf q) (417)) (countLit q [213, 214]) (countLit q [215, 216]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [213, 214]) + (countLit q [215, 216]) := List.countP_append (p := literal q) (l₁ := [213, 214]) (l₂ := [215, 216])
  have hm := merge_left (literal (valuationOf q) (413)) (literal (valuationOf q) (417)) (countLit q [213, 214]) (countLit q [215, 216]) (count417 q) 1 (meaning413 q) (meaning417 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 417 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [210, 211, 212]) + (countLit q [213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212]) (l₂ := [213, 214, 215, 216])
  have hm := merge_right (literal (valuationOf q) (417)) (literal (valuationOf q) (419)) (countLit q [210, 211, 212]) (countLit q [213, 214, 215, 216]) (count419 q) 1 (meaning417 q) (meaning419 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [210, 211, 212]) + (countLit q [213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212]) (l₂ := [213, 214, 215, 216])
  have hm := merge_left (literal (valuationOf q) (411)) (literal (valuationOf q) (419)) (countLit q [210, 211, 212]) (countLit q [213, 214, 215, 216]) (count419 q) 1 (meaning411 q) (meaning419 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 419 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216])
  have hm := merge_right (literal (valuationOf q) (419)) (literal (valuationOf q) (421)) (countLit q [203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216]) (count421 q) 1 (meaning419 q) (meaning421 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 421 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_right (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (423)) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count423 q) 1 (meaning395 q) (meaning423 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 423 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 421 = false ∨ valuationOf q 424 = true := by
  have hs : count423 q = (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_two (literal (valuationOf q) (395)) (literal (valuationOf q) (421)) (literal (valuationOf q) (424)) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count423 q) 1 1 (meaning395 q) (meaning421 q) (meaning424 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 421 = false ∨ valuationOf q 424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 421 = false ∨ valuation q 424 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 396 = false ∨ valuationOf q 424 = true := by
  have hs : count423 q = (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_left (literal (valuationOf q) (396)) (literal (valuationOf q) (424)) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count423 q) 2 (meaning396 q) (meaning424 q) hs
  change valuationOf q 396 = false ∨ valuationOf q 424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 396 = false ∨ valuation q 424 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 424 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_right (literal (valuationOf q) (424)) (literal (valuationOf q) (426)) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count425 q) 2 (meaning424 q) (meaning426 q) hs
  change valuationOf q 424 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 424 = false ∨ valuation q 426 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_left (literal (valuationOf q) (371)) (literal (valuationOf q) (425)) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count425 q) 1 (meaning371 q) (meaning425 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 425 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 423 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_two (literal (valuationOf q) (371)) (literal (valuationOf q) (423)) (literal (valuationOf q) (426)) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count425 q) 1 1 (meaning371 q) (meaning423 q) (meaning426 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 423 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 423 = false ∨ valuation q 426 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 372 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_left (literal (valuationOf q) (372)) (literal (valuationOf q) (426)) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count425 q) 2 (meaning372 q) (meaning426 q) hs
  change valuationOf q 372 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 372 = false ∨ valuation q 426 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 426 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_right (literal (valuationOf q) (426)) (literal (valuationOf q) (428)) (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count427 q) 2 (meaning426 q) (meaning428 q) hs
  change valuationOf q 426 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 426 = false ∨ valuation q 428 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_two (literal (valuationOf q) (319)) (literal (valuationOf q) (425)) (literal (valuationOf q) (428)) (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count427 q) 1 1 (meaning319 q) (meaning425 q) (meaning428 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 425 = false ∨ valuation q 428 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 320 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_left (literal (valuationOf q) (320)) (literal (valuationOf q) (428)) (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count427 q) 2 (meaning320 q) (meaning428 q) hs
  change valuationOf q 320 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 320 = false ∨ valuation q 428 = true := counterClause439 (baseVal q)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 428 = false := by
  rw [value428]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count427 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause441 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 743 = true := by
  have hs : count743 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (743)) (countLit q [-4]) (countLit q [-5]) (count743 q) 1 (meaningNeg5 q) (meaning743 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 743 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 743 = true := by
  have hs : count743 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (743)) (countLit q [-4]) (countLit q [-5]) (count743 q) 1 (meaningNeg4 q) (meaning743 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 743 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 5 = true ∨ valuationOf q 744 = true := by
  have hs : count743 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (744)) (countLit q [-4]) (countLit q [-5]) (count743 q) 1 1 (meaningNeg4 q) (meaningNeg5 q) (meaning744 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 744 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 744 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 743 = false ∨ valuationOf q 745 = true := by
  have hs : count745 q = (countLit q [-1]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (743)) (literal (valuationOf q) (745)) (countLit q [-1]) (countLit q [-4, -5]) (count745 q) 1 (meaning743 q) (meaning745 q) hs
  change valuationOf q 743 = false ∨ valuationOf q 745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 743 = false ∨ valuation q 745 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 744 = false ∨ valuationOf q 746 = true := by
  have hs : count745 q = (countLit q [-1]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (744)) (literal (valuationOf q) (746)) (countLit q [-1]) (countLit q [-4, -5]) (count745 q) 2 (meaning744 q) (meaning746 q) hs
  change valuationOf q 744 = false ∨ valuationOf q 746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 744 = false ∨ valuation q 746 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 745 = true := by
  have hs : count745 q = (countLit q [-1]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (745)) (countLit q [-1]) (countLit q [-4, -5]) (count745 q) 1 (meaningNeg1 q) (meaning745 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 745 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 745 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 743 = false ∨ valuationOf q 746 = true := by
  have hs : count745 q = (countLit q [-1]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (743)) (literal (valuationOf q) (746)) (countLit q [-1]) (countLit q [-4, -5]) (count745 q) 1 1 (meaningNeg1 q) (meaning743 q) (meaning746 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 743 = false ∨ valuationOf q 746 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 743 = false ∨ valuation q 746 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 744 = false ∨ valuationOf q 747 = true := by
  have hs : count745 q = (countLit q [-1]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (744)) (literal (valuationOf q) (747)) (countLit q [-1]) (countLit q [-4, -5]) (count745 q) 1 2 (meaningNeg1 q) (meaning744 q) (meaning747 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 744 = false ∨ valuationOf q 747 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 744 = false ∨ valuation q 747 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E185.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112185
