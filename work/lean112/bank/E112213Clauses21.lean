import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [205, 206, 207]) + (countLit q [208, 209, 210, 211]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207]) (l₂ := [208, 209, 210, 211])
  have hm := merge_left (literal (valuationOf q) (407)) (literal (valuationOf q) (415)) (countLit q [205, 206, 207]) (countLit q [208, 209, 210, 211]) (count415 q) 1 (meaning407 q) (meaning415 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 415 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [213]) + (countLit q [214]) := List.countP_append (p := literal q) (l₁ := [213]) (l₂ := [214])
  have hm := merge_left (literal (valuationOf q) (213)) (literal (valuationOf q) (417)) (countLit q [213]) (countLit q [214]) (count417 q) 1 (meaning213 q) (meaning417 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 417 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [212]) + (countLit q [213, 214]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213, 214])
  have hm := merge_right (literal (valuationOf q) (417)) (literal (valuationOf q) (419)) (countLit q [212]) (countLit q [213, 214]) (count419 q) 1 (meaning417 q) (meaning419 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [212]) + (countLit q [213, 214]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213, 214])
  have hm := merge_left (literal (valuationOf q) (212)) (literal (valuationOf q) (419)) (countLit q [212]) (countLit q [213, 214]) (count419 q) 1 (meaning212 q) (meaning419 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 419 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [215]) + (countLit q [216]) := List.countP_append (p := literal q) (l₁ := [215]) (l₂ := [216])
  have hm := merge_left (literal (valuationOf q) (215)) (literal (valuationOf q) (421)) (countLit q [215]) (countLit q [216]) (count421 q) 1 (meaning215 q) (meaning421 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 421 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [215, 216]) + (countLit q [217, 218]) := List.countP_append (p := literal q) (l₁ := [215, 216]) (l₂ := [217, 218])
  have hm := merge_left (literal (valuationOf q) (421)) (literal (valuationOf q) (425)) (countLit q [215, 216]) (countLit q [217, 218]) (count425 q) 1 (meaning421 q) (meaning425 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 425 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [212, 213, 214]) + (countLit q [215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [212, 213, 214]) (l₂ := [215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [212, 213, 214]) (countLit q [215, 216, 217, 218]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [212, 213, 214]) + (countLit q [215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [212, 213, 214]) (l₂ := [215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (427)) (countLit q [212, 213, 214]) (countLit q [215, 216, 217, 218]) (count427 q) 1 (meaning419 q) (meaning427 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 427 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [212, 213, 214]) + (countLit q [215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [212, 213, 214]) (l₂ := [215, 216, 217, 218])
  have hm := merge_two (literal (valuationOf q) (419)) (literal (valuationOf q) (425)) (literal (valuationOf q) (428)) (countLit q [212, 213, 214]) (countLit q [215, 216, 217, 218]) (count427 q) 1 1 (meaning419 q) (meaning425 q) (meaning428 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 425 = false ∨ valuation q 428 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [205, 206, 207, 208, 209, 210, 211]) + (countLit q [212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211]) (l₂ := [212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [205, 206, 207, 208, 209, 210, 211]) (countLit q [212, 213, 214, 215, 216, 217, 218]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 428 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [205, 206, 207, 208, 209, 210, 211]) + (countLit q [212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211]) (l₂ := [212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (428)) (literal (valuationOf q) (430)) (countLit q [205, 206, 207, 208, 209, 210, 211]) (countLit q [212, 213, 214, 215, 216, 217, 218]) (count429 q) 2 (meaning428 q) (meaning430 q) hs
  change valuationOf q 428 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 428 = false ∨ valuation q 430 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [205, 206, 207, 208, 209, 210, 211]) + (countLit q [212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211]) (l₂ := [212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (415)) (literal (valuationOf q) (429)) (countLit q [205, 206, 207, 208, 209, 210, 211]) (countLit q [212, 213, 214, 215, 216, 217, 218]) (count429 q) 1 (meaning415 q) (meaning429 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 429 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 427 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [205, 206, 207, 208, 209, 210, 211]) + (countLit q [212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211]) (l₂ := [212, 213, 214, 215, 216, 217, 218])
  have hm := merge_two (literal (valuationOf q) (415)) (literal (valuationOf q) (427)) (literal (valuationOf q) (430)) (countLit q [205, 206, 207, 208, 209, 210, 211]) (countLit q [212, 213, 214, 215, 216, 217, 218]) (count429 q) 1 1 (meaning415 q) (meaning427 q) (meaning430 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 427 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 427 = false ∨ valuation q 430 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [219]) + (countLit q [220, 222]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220, 222])
  have hm := merge_left (literal (valuationOf q) (219)) (literal (valuationOf q) (433)) (countLit q [219]) (countLit q [220, 222]) (count433 q) 1 (meaning219 q) (meaning433 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 433 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 224 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [223]) + (countLit q [224]) := List.countP_append (p := literal q) (l₁ := [223]) (l₂ := [224])
  have hm := merge_right (literal (valuationOf q) (224)) (literal (valuationOf q) (435)) (countLit q [223]) (countLit q [224]) (count435 q) 1 (meaning224 q) (meaning435 q) hs
  change valuationOf q 224 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 224 = false ∨ valuation q 435 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_right (literal (valuationOf q) (226)) (literal (valuationOf q) (437)) (countLit q [225]) (countLit q [226]) (count437 q) 1 (meaning226 q) (meaning437 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 437 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [223, 224]) + (countLit q [225, 226]) := List.countP_append (p := literal q) (l₁ := [223, 224]) (l₂ := [225, 226])
  have hm := merge_right (literal (valuationOf q) (437)) (literal (valuationOf q) (439)) (countLit q [223, 224]) (countLit q [225, 226]) (count439 q) 1 (meaning437 q) (meaning439 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 439 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [223, 224]) + (countLit q [225, 226]) := List.countP_append (p := literal q) (l₁ := [223, 224]) (l₂ := [225, 226])
  have hm := merge_left (literal (valuationOf q) (435)) (literal (valuationOf q) (439)) (countLit q [223, 224]) (countLit q [225, 226]) (count439 q) 1 (meaning435 q) (meaning439 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 439 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [219, 220, 222]) + (countLit q [223, 224, 225, 226]) := List.countP_append (p := literal q) (l₁ := [219, 220, 222]) (l₂ := [223, 224, 225, 226])
  have hm := merge_right (literal (valuationOf q) (439)) (literal (valuationOf q) (441)) (countLit q [219, 220, 222]) (countLit q [223, 224, 225, 226]) (count441 q) 1 (meaning439 q) (meaning441 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 441 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [219, 220, 222]) + (countLit q [223, 224, 225, 226]) := List.countP_append (p := literal q) (l₁ := [219, 220, 222]) (l₂ := [223, 224, 225, 226])
  have hm := merge_left (literal (valuationOf q) (433)) (literal (valuationOf q) (441)) (countLit q [219, 220, 222]) (countLit q [223, 224, 225, 226]) (count441 q) 1 (meaning433 q) (meaning441 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 441 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [227]) + (countLit q [228]) := List.countP_append (p := literal q) (l₁ := [227]) (l₂ := [228])
  have hm := merge_right (literal (valuationOf q) (228)) (literal (valuationOf q) (443)) (countLit q [227]) (countLit q [228]) (count443 q) 1 (meaning228 q) (meaning443 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 443 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [227, 228]) + (countLit q [229, 230]) := List.countP_append (p := literal q) (l₁ := [227, 228]) (l₂ := [229, 230])
  have hm := merge_left (literal (valuationOf q) (443)) (literal (valuationOf q) (447)) (countLit q [227, 228]) (countLit q [229, 230]) (count447 q) 1 (meaning443 q) (meaning447 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 447 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 232 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_right (literal (valuationOf q) (232)) (literal (valuationOf q) (449)) (countLit q [231]) (countLit q [232]) (count449 q) 1 (meaning232 q) (meaning449 q) hs
  change valuationOf q 232 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 449 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [231, 232]) + (countLit q [233, 234]) := List.countP_append (p := literal q) (l₁ := [231, 232]) (l₂ := [233, 234])
  have hm := merge_left (literal (valuationOf q) (449)) (literal (valuationOf q) (453)) (countLit q [231, 232]) (countLit q [233, 234]) (count453 q) 1 (meaning449 q) (meaning453 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 453 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [227, 228, 229, 230]) + (countLit q [231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [227, 228, 229, 230]) (l₂ := [231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [227, 228, 229, 230]) (countLit q [231, 232, 233, 234]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [227, 228, 229, 230]) + (countLit q [231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [227, 228, 229, 230]) (l₂ := [231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (447)) (literal (valuationOf q) (455)) (countLit q [227, 228, 229, 230]) (countLit q [231, 232, 233, 234]) (count455 q) 1 (meaning447 q) (meaning455 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 455 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [219, 220, 222, 223, 224, 225, 226]) + (countLit q [227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [219, 220, 222, 223, 224, 225, 226]) (l₂ := [227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (countLit q [219, 220, 222, 223, 224, 225, 226]) (countLit q [227, 228, 229, 230, 231, 232, 233, 234]) (count457 q) 1 (meaning455 q) (meaning457 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [219, 220, 222, 223, 224, 225, 226]) + (countLit q [227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [219, 220, 222, 223, 224, 225, 226]) (l₂ := [227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (441)) (literal (valuationOf q) (457)) (countLit q [219, 220, 222, 223, 224, 225, 226]) (countLit q [227, 228, 229, 230, 231, 232, 233, 234]) (count457 q) 1 (meaning441 q) (meaning457 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 457 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) + (countLit q [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (l₂ := [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (457)) (literal (valuationOf q) (459)) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (countLit q [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count459 q) 1 (meaning457 q) (meaning459 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 459 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) + (countLit q [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (l₂ := [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (429)) (literal (valuationOf q) (459)) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (countLit q [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count459 q) 1 (meaning429 q) (meaning459 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 459 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) + (countLit q [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (l₂ := [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_two (literal (valuationOf q) (429)) (literal (valuationOf q) (457)) (literal (valuationOf q) (460)) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (countLit q [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count459 q) 1 1 (meaning429 q) (meaning457 q) (meaning460 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 457 = false ∨ valuation q 460 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 430 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) + (countLit q [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (l₂ := [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (430)) (literal (valuationOf q) (460)) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (countLit q [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count459 q) 2 (meaning430 q) (meaning460 q) hs
  change valuationOf q 430 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 430 = false ∨ valuation q 460 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E213.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112213
