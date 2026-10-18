import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 214 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_left (literal (valuationOf q) (214)) (literal (valuationOf q) (415)) (countLit q [214]) (countLit q [215]) (count415 q) 1 (meaning214 q) (meaning415 q) hs
  change valuationOf q 214 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 415 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 214 = false ∨ valuationOf q 215 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_two (literal (valuationOf q) (214)) (literal (valuationOf q) (215)) (literal (valuationOf q) (416)) (countLit q [214]) (countLit q [215]) (count415 q) 1 1 (meaning214 q) (meaning215 q) (meaning416 q) hs
  change valuationOf q 214 = false ∨ valuationOf q 215 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 215 = false ∨ valuation q 416 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [212, 213]) + (countLit q [214, 215]) := List.countP_append (p := literal q) (l₁ := [212, 213]) (l₂ := [214, 215])
  have hm := merge_right (literal (valuationOf q) (415)) (literal (valuationOf q) (417)) (countLit q [212, 213]) (countLit q [214, 215]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 416 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [212, 213]) + (countLit q [214, 215]) := List.countP_append (p := literal q) (l₁ := [212, 213]) (l₂ := [214, 215])
  have hm := merge_right (literal (valuationOf q) (416)) (literal (valuationOf q) (418)) (countLit q [212, 213]) (countLit q [214, 215]) (count417 q) 2 (meaning416 q) (meaning418 q) hs
  change valuationOf q 416 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 416 = false ∨ valuation q 418 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [212, 213]) + (countLit q [214, 215]) := List.countP_append (p := literal q) (l₁ := [212, 213]) (l₂ := [214, 215])
  have hm := merge_left (literal (valuationOf q) (413)) (literal (valuationOf q) (417)) (countLit q [212, 213]) (countLit q [214, 215]) (count417 q) 1 (meaning413 q) (meaning417 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 417 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [209, 210, 211]) + (countLit q [212, 213, 214, 215]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211]) (l₂ := [212, 213, 214, 215])
  have hm := merge_right (literal (valuationOf q) (417)) (literal (valuationOf q) (419)) (countLit q [209, 210, 211]) (countLit q [212, 213, 214, 215]) (count419 q) 1 (meaning417 q) (meaning419 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [209, 210, 211]) + (countLit q [212, 213, 214, 215]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211]) (l₂ := [212, 213, 214, 215])
  have hm := merge_right (literal (valuationOf q) (418)) (literal (valuationOf q) (420)) (countLit q [209, 210, 211]) (countLit q [212, 213, 214, 215]) (count419 q) 2 (meaning418 q) (meaning420 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 420 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [209, 210, 211]) + (countLit q [212, 213, 214, 215]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211]) (l₂ := [212, 213, 214, 215])
  have hm := merge_left (literal (valuationOf q) (411)) (literal (valuationOf q) (419)) (countLit q [209, 210, 211]) (countLit q [212, 213, 214, 215]) (count419 q) 1 (meaning411 q) (meaning419 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 419 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 417 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [209, 210, 211]) + (countLit q [212, 213, 214, 215]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211]) (l₂ := [212, 213, 214, 215])
  have hm := merge_two (literal (valuationOf q) (411)) (literal (valuationOf q) (417)) (literal (valuationOf q) (420)) (countLit q [209, 210, 211]) (countLit q [212, 213, 214, 215]) (count419 q) 1 1 (meaning411 q) (meaning417 q) (meaning420 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 417 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 417 = false ∨ valuation q 420 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (421)) (countLit q [217]) (countLit q [218]) (count421 q) 1 (meaning217 q) (meaning421 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 421 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [216]) + (countLit q [217, 218]) := List.countP_append (p := literal q) (l₁ := [216]) (l₂ := [217, 218])
  have hm := merge_right (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (countLit q [216]) (countLit q [217, 218]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [219]) + (countLit q [220]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220])
  have hm := merge_right (literal (valuationOf q) (220)) (literal (valuationOf q) (425)) (countLit q [219]) (countLit q [220]) (count425 q) 1 (meaning220 q) (meaning425 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 425 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [221]) + (countLit q [222]) := List.countP_append (p := literal q) (l₁ := [221]) (l₂ := [222])
  have hm := merge_right (literal (valuationOf q) (222)) (literal (valuationOf q) (427)) (countLit q [221]) (countLit q [222]) (count427 q) 1 (meaning222 q) (meaning427 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 427 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [219, 220]) + (countLit q [221, 222]) := List.countP_append (p := literal q) (l₁ := [219, 220]) (l₂ := [221, 222])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [219, 220]) (countLit q [221, 222]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [219, 220]) + (countLit q [221, 222]) := List.countP_append (p := literal q) (l₁ := [219, 220]) (l₂ := [221, 222])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (429)) (countLit q [219, 220]) (countLit q [221, 222]) (count429 q) 1 (meaning425 q) (meaning429 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 429 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [216, 217, 218]) + (countLit q [219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [216, 217, 218]) (l₂ := [219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [216, 217, 218]) (countLit q [219, 220, 221, 222]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [216, 217, 218]) + (countLit q [219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [216, 217, 218]) (l₂ := [219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (423)) (literal (valuationOf q) (431)) (countLit q [216, 217, 218]) (countLit q [219, 220, 221, 222]) (count431 q) 1 (meaning423 q) (meaning431 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 431 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (431)) (literal (valuationOf q) (433)) (countLit q [209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222]) (count433 q) 1 (meaning431 q) (meaning433 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 433 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (433)) (countLit q [209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222]) (count433 q) 1 (meaning419 q) (meaning433 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 433 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (419)) (literal (valuationOf q) (431)) (literal (valuationOf q) (434)) (countLit q [209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222]) (count433 q) 1 1 (meaning419 q) (meaning431 q) (meaning434 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 431 = false ∨ valuation q 434 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 420 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (420)) (literal (valuationOf q) (434)) (countLit q [209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222]) (count433 q) 2 (meaning420 q) (meaning434 q) hs
  change valuationOf q 420 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 420 = false ∨ valuation q 434 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (433)) (literal (valuationOf q) (435)) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 (meaning433 q) (meaning435 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 435 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 434 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (434)) (literal (valuationOf q) (436)) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 2 (meaning434 q) (meaning436 q) hs
  change valuationOf q 434 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 434 = false ∨ valuation q 436 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (407)) (literal (valuationOf q) (435)) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 (meaning407 q) (meaning435 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 435 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (407)) (literal (valuationOf q) (433)) (literal (valuationOf q) (436)) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 1 (meaning407 q) (meaning433 q) (meaning436 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 433 = false ∨ valuation q 436 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 408 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (408)) (literal (valuationOf q) (436)) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 2 (meaning408 q) (meaning436 q) hs
  change valuationOf q 408 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 408 = false ∨ valuation q 436 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 436 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (436)) (literal (valuationOf q) (438)) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 2 (meaning436 q) (meaning438 q) hs
  change valuationOf q 436 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 436 = false ∨ valuation q 438 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (437)) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 (meaning381 q) (meaning437 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 437 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 435 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (381)) (literal (valuationOf q) (435)) (literal (valuationOf q) (438)) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 1 (meaning381 q) (meaning435 q) (meaning438 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 435 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 435 = false ∨ valuation q 438 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 382 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (382)) (literal (valuationOf q) (438)) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 2 (meaning382 q) (meaning438 q) hs
  change valuationOf q 382 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 382 = false ∨ valuation q 438 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 438 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (438)) (literal (valuationOf q) (440)) (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count439 q) 2 (meaning438 q) (meaning440 q) hs
  change valuationOf q 438 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 438 = false ∨ valuation q 440 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E161.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112161
