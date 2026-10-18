import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [220, 221]) + (countLit q [222, 223]) := List.countP_append (p := literal q) (l₁ := [220, 221]) (l₂ := [222, 223])
  have hm := merge_left (literal (valuationOf q) (429)) (literal (valuationOf q) (433)) (countLit q [220, 221]) (countLit q [222, 223]) (count433 q) 1 (meaning429 q) (meaning433 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 433 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [216, 217, 218, 219]) + (countLit q [220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [216, 217, 218, 219]) (l₂ := [220, 221, 222, 223])
  have hm := merge_right (literal (valuationOf q) (433)) (literal (valuationOf q) (435)) (countLit q [216, 217, 218, 219]) (countLit q [220, 221, 222, 223]) (count435 q) 1 (meaning433 q) (meaning435 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 435 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [216, 217, 218, 219]) + (countLit q [220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [216, 217, 218, 219]) (l₂ := [220, 221, 222, 223])
  have hm := merge_left (literal (valuationOf q) (427)) (literal (valuationOf q) (435)) (countLit q [216, 217, 218, 219]) (countLit q [220, 221, 222, 223]) (count435 q) 1 (meaning427 q) (meaning435 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 435 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222, 223])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222, 223])
  have hm := merge_left (literal (valuationOf q) (421)) (literal (valuationOf q) (437)) (countLit q [209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222, 223]) (count437 q) 1 (meaning421 q) (meaning437 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 437 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal q) (l₁ := [229]) (l₂ := [230])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (445)) (countLit q [229]) (countLit q [230]) (count445 q) 1 (meaning229 q) (meaning445 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 445 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [227, 228]) + (countLit q [229, 230]) := List.countP_append (p := literal q) (l₁ := [227, 228]) (l₂ := [229, 230])
  have hm := merge_right (literal (valuationOf q) (445)) (literal (valuationOf q) (447)) (countLit q [227, 228]) (countLit q [229, 230]) (count447 q) 1 (meaning445 q) (meaning447 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 447 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [224, 225, 226]) + (countLit q [227, 228, 229, 230]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226]) (l₂ := [227, 228, 229, 230])
  have hm := merge_right (literal (valuationOf q) (447)) (literal (valuationOf q) (449)) (countLit q [224, 225, 226]) (countLit q [227, 228, 229, 230]) (count449 q) 1 (meaning447 q) (meaning449 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 449 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [237]) + (countLit q [238]) := List.countP_append (p := literal q) (l₁ := [237]) (l₂ := [238])
  have hm := merge_right (literal (valuationOf q) (238)) (literal (valuationOf q) (459)) (countLit q [237]) (countLit q [238]) (count459 q) 1 (meaning238 q) (meaning459 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 459 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [235, 236]) + (countLit q [237, 238]) := List.countP_append (p := literal q) (l₁ := [235, 236]) (l₂ := [237, 238])
  have hm := merge_right (literal (valuationOf q) (459)) (literal (valuationOf q) (461)) (countLit q [235, 236]) (countLit q [237, 238]) (count461 q) 1 (meaning459 q) (meaning461 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [231, 232, 233, 234]) + (countLit q [235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [231, 232, 233, 234]) (l₂ := [235, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (461)) (literal (valuationOf q) (463)) (countLit q [231, 232, 233, 234]) (countLit q [235, 236, 237, 238]) (count463 q) 1 (meaning461 q) (meaning463 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 463 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (463)) (literal (valuationOf q) (465)) (countLit q [224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) (count465 q) 1 (meaning463 q) (meaning465 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 465 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (449)) (literal (valuationOf q) (465)) (countLit q [224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) (count465 q) 1 (meaning449 q) (meaning465 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 465 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_two (literal (valuationOf q) (449)) (literal (valuationOf q) (463)) (literal (valuationOf q) (466)) (countLit q [224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) (count465 q) 1 1 (meaning449 q) (meaning463 q) (meaning466 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 463 = false ∨ valuation q 466 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) + (countLit q [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (l₂ := [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (countLit q [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 466 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) + (countLit q [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (l₂ := [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (466)) (literal (valuationOf q) (468)) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (countLit q [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (count467 q) 2 (meaning466 q) (meaning468 q) hs
  change valuationOf q 466 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 466 = false ∨ valuation q 468 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) + (countLit q [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (l₂ := [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (467)) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (countLit q [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (count467 q) 1 (meaning437 q) (meaning467 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 467 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) + (countLit q [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (l₂ := [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_two (literal (valuationOf q) (437)) (literal (valuationOf q) (465)) (literal (valuationOf q) (468)) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]) (countLit q [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (count467 q) 1 1 (meaning437 q) (meaning465 q) (meaning468 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 465 = false ∨ valuation q 468 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (467)) (literal (valuationOf q) (469)) (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (count469 q) 1 (meaning467 q) (meaning469 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 469 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 468 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (468)) (literal (valuationOf q) (470)) (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (count469 q) 2 (meaning468 q) (meaning470 q) hs
  change valuationOf q 468 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 468 = false ∨ valuation q 470 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (409)) (literal (valuationOf q) (469)) (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (count469 q) 1 (meaning409 q) (meaning469 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 469 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 467 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_two (literal (valuationOf q) (409)) (literal (valuationOf q) (467)) (literal (valuationOf q) (470)) (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (count469 q) 1 1 (meaning409 q) (meaning467 q) (meaning470 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 467 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 467 = false ∨ valuation q 470 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (410)) (literal (valuationOf q) (470)) (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (count469 q) 2 (meaning410 q) (meaning470 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 470 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 470 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (470)) (literal (valuationOf q) (472)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (count471 q) 2 (meaning470 q) (meaning472 q) hs
  change valuationOf q 470 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 470 = false ∨ valuation q 472 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_two (literal (valuationOf q) (353)) (literal (valuationOf q) (469)) (literal (valuationOf q) (472)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (count471 q) 1 1 (meaning353 q) (meaning469 q) (meaning472 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 469 = false ∨ valuation q 472 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 354 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (354)) (literal (valuationOf q) (472)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (count471 q) 2 (meaning354 q) (meaning472 q) hs
  change valuationOf q 354 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 354 = false ∨ valuation q 472 = true := counterClause730 (baseVal q)

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 472 = false := by
  rw [value472]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count471 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause732 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1447 = true := by
  have hs : count1447 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1447)) (countLit q [-4]) (countLit q [-5]) (count1447 q) 1 (meaningNeg5 q) (meaning1447 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1447 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1447 = true := by
  have hs : count1447 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1447)) (countLit q [-4]) (countLit q [-5]) (count1447 q) 1 (meaningNeg4 q) (meaning1447 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1447 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1448 = true := by
  have hs : count1447 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1448)) (countLit q [-4]) (countLit q [-5]) (count1447 q) 1 1 (meaningNeg4 q) (meaningNeg5 q) (meaning1448 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 1448 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1449 = true := by
  have hs : count1449 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1449)) (countLit q [-2]) (countLit q [-4, -5]) (count1449 q) 1 (meaning1447 q) (meaning1449 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1449 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1450)) (countLit q [-2]) (countLit q [-4, -5]) (count1449 q) 2 (meaning1448 q) (meaning1450 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1450 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E078.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112078
