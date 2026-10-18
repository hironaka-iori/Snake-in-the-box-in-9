import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (423)) (countLit q [214, 215]) (countLit q [216, 217]) (count423 q) 1 (meaning419 q) (meaning423 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 423 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [218]) + (countLit q [219]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219])
  have hm := merge_left (literal (valuationOf q) (218)) (literal (valuationOf q) (425)) (countLit q [218]) (countLit q [219]) (count425 q) 1 (meaning218 q) (meaning425 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 425 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [220]) + (countLit q [221]) := List.countP_append (p := literal q) (l₁ := [220]) (l₂ := [221])
  have hm := merge_right (literal (valuationOf q) (221)) (literal (valuationOf q) (427)) (countLit q [220]) (countLit q [221]) (count427 q) 1 (meaning221 q) (meaning427 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 427 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [218, 219]) + (countLit q [220, 221]) := List.countP_append (p := literal q) (l₁ := [218, 219]) (l₂ := [220, 221])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [218, 219]) (countLit q [220, 221]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [218, 219]) + (countLit q [220, 221]) := List.countP_append (p := literal q) (l₁ := [218, 219]) (l₂ := [220, 221])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (429)) (countLit q [218, 219]) (countLit q [220, 221]) (count429 q) 1 (meaning425 q) (meaning429 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 429 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (423)) (literal (valuationOf q) (431)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 1 (meaning423 q) (meaning431 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 431 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (431)) (literal (valuationOf q) (433)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 1 (meaning431 q) (meaning433 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 433 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (433)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 1 (meaning417 q) (meaning433 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 433 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_two (literal (valuationOf q) (417)) (literal (valuationOf q) (431)) (literal (valuationOf q) (434)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 1 1 (meaning417 q) (meaning431 q) (meaning434 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 431 = false ∨ valuation q 434 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [222]) (l₂ := [223, 224])
  have hm := merge_left (literal (valuationOf q) (222)) (literal (valuationOf q) (437)) (countLit q [222]) (countLit q [223, 224]) (count437 q) 1 (meaning222 q) (meaning437 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 437 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (445)) (countLit q [222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 (meaning437 q) (meaning445 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 445 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 232 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_right (literal (valuationOf q) (232)) (literal (valuationOf q) (449)) (countLit q [231]) (countLit q [232]) (count449 q) 1 (meaning232 q) (meaning449 q) hs
  change valuationOf q 232 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 449 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (449)) (countLit q [231]) (countLit q [232]) (count449 q) 1 (meaning231 q) (meaning449 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 449 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 232 = false ∨ valuationOf q 450 = true := by
  have hs : count449 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_two (literal (valuationOf q) (231)) (literal (valuationOf q) (232)) (literal (valuationOf q) (450)) (countLit q [231]) (countLit q [232]) (count449 q) 1 1 (meaning231 q) (meaning232 q) (meaning450 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 232 = false ∨ valuationOf q 450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 232 = false ∨ valuation q 450 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_right (literal (valuationOf q) (449)) (literal (valuationOf q) (451)) (countLit q [229, 230]) (countLit q [231, 232]) (count451 q) 1 (meaning449 q) (meaning451 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 451 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 450 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_right (literal (valuationOf q) (450)) (literal (valuationOf q) (452)) (countLit q [229, 230]) (countLit q [231, 232]) (count451 q) 2 (meaning450 q) (meaning452 q) hs
  change valuationOf q 450 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 450 = false ∨ valuation q 452 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_right (literal (valuationOf q) (234)) (literal (valuationOf q) (453)) (countLit q [233]) (countLit q [234]) (count453 q) 1 (meaning234 q) (meaning453 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 453 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [235]) + (countLit q [236]) := List.countP_append (p := literal q) (l₁ := [235]) (l₂ := [236])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (455)) (countLit q [235]) (countLit q [236]) (count455 q) 1 (meaning235 q) (meaning455 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 455 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_right (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (countLit q [233, 234]) (countLit q [235, 236]) (count457 q) 1 (meaning455 q) (meaning457 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_left (literal (valuationOf q) (453)) (literal (valuationOf q) (457)) (countLit q [233, 234]) (countLit q [235, 236]) (count457 q) 1 (meaning453 q) (meaning457 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 457 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (457)) (literal (valuationOf q) (459)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count459 q) 1 (meaning457 q) (meaning459 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 459 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (451)) (literal (valuationOf q) (459)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count459 q) 1 (meaning451 q) (meaning459 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 459 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (451)) (literal (valuationOf q) (457)) (literal (valuationOf q) (460)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count459 q) 1 1 (meaning451 q) (meaning457 q) (meaning460 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 457 = false ∨ valuation q 460 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 452 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (452)) (literal (valuationOf q) (460)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count459 q) 2 (meaning452 q) (meaning460 q) hs
  change valuationOf q 452 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 452 = false ∨ valuation q 460 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (459)) (literal (valuationOf q) (461)) (countLit q [222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (count461 q) 1 (meaning459 q) (meaning461 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 460 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (460)) (literal (valuationOf q) (462)) (countLit q [222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (count461 q) 2 (meaning460 q) (meaning462 q) hs
  change valuationOf q 460 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 460 = false ∨ valuation q 462 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (445)) (literal (valuationOf q) (461)) (countLit q [222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (count461 q) 1 (meaning445 q) (meaning461 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 461 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (461)) (literal (valuationOf q) (463)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 1 (meaning461 q) (meaning463 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 463 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 462 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (462)) (literal (valuationOf q) (464)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 2 (meaning462 q) (meaning464 q) hs
  change valuationOf q 462 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 462 = false ∨ valuation q 464 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (433)) (literal (valuationOf q) (463)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 1 (meaning433 q) (meaning463 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 463 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (433)) (literal (valuationOf q) (461)) (literal (valuationOf q) (464)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 1 1 (meaning433 q) (meaning461 q) (meaning464 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 461 = false ∨ valuation q 464 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E104.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112104
