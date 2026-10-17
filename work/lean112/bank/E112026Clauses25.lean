import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [224, 225]) + (countLit q [226, 227]) := List.countP_append (p := literal q) (l₁ := [224, 225]) (l₂ := [226, 227])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (441)) (countLit q [224, 225]) (countLit q [226, 227]) (count441 q) 1 (meaning437 q) (meaning441 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 441 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [220, 221, 222, 223]) + (countLit q [224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [220, 221, 222, 223]) (l₂ := [224, 225, 226, 227])
  have hm := merge_right (literal (valuationOf q) (441)) (literal (valuationOf q) (443)) (countLit q [220, 221, 222, 223]) (countLit q [224, 225, 226, 227]) (count443 q) 1 (meaning441 q) (meaning443 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 443 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [220, 221, 222, 223]) + (countLit q [224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [220, 221, 222, 223]) (l₂ := [224, 225, 226, 227])
  have hm := merge_left (literal (valuationOf q) (435)) (literal (valuationOf q) (443)) (countLit q [220, 221, 222, 223]) (countLit q [224, 225, 226, 227]) (count443 q) 1 (meaning435 q) (meaning443 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 443 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [213, 214, 215, 216, 217, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227])
  have hm := merge_right (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (countLit q [213, 214, 215, 216, 217, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [213, 214, 215, 216, 217, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227])
  have hm := merge_left (literal (valuationOf q) (429)) (literal (valuationOf q) (445)) (countLit q [213, 214, 215, 216, 217, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) (count445 q) 1 (meaning429 q) (meaning445 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 445 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 443 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [213, 214, 215, 216, 217, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227])
  have hm := merge_two (literal (valuationOf q) (429)) (literal (valuationOf q) (443)) (literal (valuationOf q) (446)) (countLit q [213, 214, 215, 216, 217, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) (count445 q) 1 1 (meaning429 q) (meaning443 q) (meaning446 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 443 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 443 = false ∨ valuation q 446 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 230 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal q) (l₁ := [229]) (l₂ := [230])
  have hm := merge_right (literal (valuationOf q) (230)) (literal (valuationOf q) (447)) (countLit q [229]) (countLit q [230]) (count447 q) 1 (meaning230 q) (meaning447 q) hs
  change valuationOf q 230 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 447 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [228]) + (countLit q [229, 230]) := List.countP_append (p := literal q) (l₁ := [228]) (l₂ := [229, 230])
  have hm := merge_right (literal (valuationOf q) (447)) (literal (valuationOf q) (449)) (countLit q [228]) (countLit q [229, 230]) (count449 q) 1 (meaning447 q) (meaning449 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 449 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_right (literal (valuationOf q) (234)) (literal (valuationOf q) (453)) (countLit q [233]) (countLit q [234]) (count453 q) 1 (meaning234 q) (meaning453 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 453 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (453)) (countLit q [233]) (countLit q [234]) (count453 q) 1 (meaning233 q) (meaning453 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 453 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [231, 232]) + (countLit q [233, 234]) := List.countP_append (p := literal q) (l₁ := [231, 232]) (l₂ := [233, 234])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [231, 232]) (countLit q [233, 234]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [228, 229, 230]) + (countLit q [231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230]) (l₂ := [231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (countLit q [228, 229, 230]) (countLit q [231, 232, 233, 234]) (count457 q) 1 (meaning455 q) (meaning457 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [228, 229, 230]) + (countLit q [231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230]) (l₂ := [231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (449)) (literal (valuationOf q) (457)) (countLit q [228, 229, 230]) (countLit q [231, 232, 233, 234]) (count457 q) 1 (meaning449 q) (meaning457 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 457 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [235]) + (countLit q [236]) := List.countP_append (p := literal q) (l₁ := [235]) (l₂ := [236])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (459)) (countLit q [235]) (countLit q [236]) (count459 q) 1 (meaning235 q) (meaning459 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 459 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [235, 236]) + (countLit q [237, 238]) := List.countP_append (p := literal q) (l₁ := [235, 236]) (l₂ := [237, 238])
  have hm := merge_left (literal (valuationOf q) (459)) (literal (valuationOf q) (463)) (countLit q [235, 236]) (countLit q [237, 238]) (count463 q) 1 (meaning459 q) (meaning463 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 463 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [241]) + (countLit q [242]) := List.countP_append (p := literal q) (l₁ := [241]) (l₂ := [242])
  have hm := merge_left (literal (valuationOf q) (241)) (literal (valuationOf q) (467)) (countLit q [241]) (countLit q [242]) (count467 q) 1 (meaning241 q) (meaning467 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 467 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [239, 240]) + (countLit q [241, 242]) := List.countP_append (p := literal q) (l₁ := [239, 240]) (l₂ := [241, 242])
  have hm := merge_right (literal (valuationOf q) (467)) (literal (valuationOf q) (469)) (countLit q [239, 240]) (countLit q [241, 242]) (count469 q) 1 (meaning467 q) (meaning469 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 469 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [235, 236, 237, 238]) + (countLit q [239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [235, 236, 237, 238]) (l₂ := [239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (469)) (literal (valuationOf q) (471)) (countLit q [235, 236, 237, 238]) (countLit q [239, 240, 241, 242]) (count471 q) 1 (meaning469 q) (meaning471 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 471 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [235, 236, 237, 238]) + (countLit q [239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [235, 236, 237, 238]) (l₂ := [239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (463)) (literal (valuationOf q) (471)) (countLit q [235, 236, 237, 238]) (countLit q [239, 240, 241, 242]) (count471 q) 1 (meaning463 q) (meaning471 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 471 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [228, 229, 230, 231, 232, 233, 234]) + (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230, 231, 232, 233, 234]) (l₂ := [235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (471)) (literal (valuationOf q) (473)) (countLit q [228, 229, 230, 231, 232, 233, 234]) (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) (count473 q) 1 (meaning471 q) (meaning473 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 473 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [228, 229, 230, 231, 232, 233, 234]) + (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230, 231, 232, 233, 234]) (l₂ := [235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (457)) (literal (valuationOf q) (473)) (countLit q [228, 229, 230, 231, 232, 233, 234]) (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) (count473 q) 1 (meaning457 q) (meaning473 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 473 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 471 = false ∨ valuationOf q 474 = true := by
  have hs : count473 q = (countLit q [228, 229, 230, 231, 232, 233, 234]) + (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230, 231, 232, 233, 234]) (l₂ := [235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_two (literal (valuationOf q) (457)) (literal (valuationOf q) (471)) (literal (valuationOf q) (474)) (countLit q [228, 229, 230, 231, 232, 233, 234]) (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) (count473 q) 1 1 (meaning457 q) (meaning471 q) (meaning474 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 471 = false ∨ valuationOf q 474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 471 = false ∨ valuation q 474 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (473)) (literal (valuationOf q) (475)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 1 (meaning473 q) (meaning475 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 475 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 474 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (474)) (literal (valuationOf q) (476)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 2 (meaning474 q) (meaning476 q) hs
  change valuationOf q 474 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 474 = false ∨ valuation q 476 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (445)) (literal (valuationOf q) (475)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 1 (meaning445 q) (meaning475 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 475 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_two (literal (valuationOf q) (445)) (literal (valuationOf q) (473)) (literal (valuationOf q) (476)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 1 1 (meaning445 q) (meaning473 q) (meaning476 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 473 = false ∨ valuation q 476 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 446 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (446)) (literal (valuationOf q) (476)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 2 (meaning446 q) (meaning476 q) hs
  change valuationOf q 446 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 446 = false ∨ valuation q 476 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (475)) (literal (valuationOf q) (477)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 1 (meaning475 q) (meaning477 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 477 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 476 = false ∨ valuationOf q 478 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (476)) (literal (valuationOf q) (478)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 2 (meaning476 q) (meaning478 q) hs
  change valuationOf q 476 = false ∨ valuationOf q 478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 476 = false ∨ valuation q 478 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (477)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 1 (meaning417 q) (meaning477 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 477 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 475 = false ∨ valuationOf q 478 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_two (literal (valuationOf q) (417)) (literal (valuationOf q) (475)) (literal (valuationOf q) (478)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 1 1 (meaning417 q) (meaning475 q) (meaning478 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 475 = false ∨ valuationOf q 478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 475 = false ∨ valuation q 478 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 478 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (418)) (literal (valuationOf q) (478)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 2 (meaning418 q) (meaning478 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 478 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E026.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112026
