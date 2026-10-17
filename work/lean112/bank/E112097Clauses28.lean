import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 242 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [241]) + (countLit q [242]) := List.countP_append (p := literal q) (l₁ := [241]) (l₂ := [242])
  have hm := merge_right (literal (valuationOf q) (242)) (literal (valuationOf q) (469)) (countLit q [241]) (countLit q [242]) (count469 q) 1 (meaning242 q) (meaning469 q) hs
  change valuationOf q 242 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 469 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [239, 240]) + (countLit q [241, 242]) := List.countP_append (p := literal q) (l₁ := [239, 240]) (l₂ := [241, 242])
  have hm := merge_right (literal (valuationOf q) (469)) (literal (valuationOf q) (471)) (countLit q [239, 240]) (countLit q [241, 242]) (count471 q) 1 (meaning469 q) (meaning471 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 471 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [243]) + (countLit q [244]) := List.countP_append (p := literal q) (l₁ := [243]) (l₂ := [244])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (473)) (countLit q [243]) (countLit q [244]) (count473 q) 1 (meaning243 q) (meaning473 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 473 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [243, 244]) + (countLit q [245, 246]) := List.countP_append (p := literal q) (l₁ := [243, 244]) (l₂ := [245, 246])
  have hm := merge_left (literal (valuationOf q) (473)) (literal (valuationOf q) (477)) (countLit q [243, 244]) (countLit q [245, 246]) (count477 q) 1 (meaning473 q) (meaning477 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 477 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_right (literal (valuationOf q) (477)) (literal (valuationOf q) (479)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count479 q) 1 (meaning477 q) (meaning479 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 479 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_left (literal (valuationOf q) (471)) (literal (valuationOf q) (479)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count479 q) 1 (meaning471 q) (meaning479 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 479 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_two (literal (valuationOf q) (471)) (literal (valuationOf q) (477)) (literal (valuationOf q) (480)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count479 q) 1 1 (meaning471 q) (meaning477 q) (meaning480 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 477 = false ∨ valuation q 480 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 479 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_right (literal (valuationOf q) (479)) (literal (valuationOf q) (481)) (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (count481 q) 1 (meaning479 q) (meaning481 q) hs
  change valuationOf q 479 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 479 = false ∨ valuation q 481 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 480 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_right (literal (valuationOf q) (480)) (literal (valuationOf q) (482)) (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (count481 q) 2 (meaning480 q) (meaning482 q) hs
  change valuationOf q 480 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 480 = false ∨ valuation q 482 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_left (literal (valuationOf q) (465)) (literal (valuationOf q) (481)) (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (count481 q) 1 (meaning465 q) (meaning481 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 481 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_right (literal (valuationOf q) (481)) (literal (valuationOf q) (483)) (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count483 q) 1 (meaning481 q) (meaning483 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 483 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 482 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_right (literal (valuationOf q) (482)) (literal (valuationOf q) (484)) (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count483 q) 2 (meaning482 q) (meaning484 q) hs
  change valuationOf q 482 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 482 = false ∨ valuation q 484 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_left (literal (valuationOf q) (451)) (literal (valuationOf q) (483)) (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count483 q) 1 (meaning451 q) (meaning483 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 483 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 481 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_two (literal (valuationOf q) (451)) (literal (valuationOf q) (481)) (literal (valuationOf q) (484)) (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count483 q) 1 1 (meaning451 q) (meaning481 q) (meaning484 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 481 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 481 = false ∨ valuation q 484 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 452 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_left (literal (valuationOf q) (452)) (literal (valuationOf q) (484)) (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count483 q) 2 (meaning452 q) (meaning484 q) hs
  change valuationOf q 452 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 452 = false ∨ valuation q 484 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 483 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_right (literal (valuationOf q) (483)) (literal (valuationOf q) (485)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count485 q) 1 (meaning483 q) (meaning485 q) hs
  change valuationOf q 483 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 483 = false ∨ valuation q 485 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 484 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_right (literal (valuationOf q) (484)) (literal (valuationOf q) (486)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count485 q) 2 (meaning484 q) (meaning486 q) hs
  change valuationOf q 484 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 484 = false ∨ valuation q 486 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_left (literal (valuationOf q) (423)) (literal (valuationOf q) (485)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count485 q) 1 (meaning423 q) (meaning485 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 485 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 483 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_two (literal (valuationOf q) (423)) (literal (valuationOf q) (483)) (literal (valuationOf q) (486)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count485 q) 1 1 (meaning423 q) (meaning483 q) (meaning486 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 483 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 483 = false ∨ valuation q 486 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 424 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) + (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) (l₂ := [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_left (literal (valuationOf q) (424)) (literal (valuationOf q) (486)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]) (countLit q [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count485 q) 2 (meaning424 q) (meaning486 q) hs
  change valuationOf q 424 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 424 = false ∨ valuation q 486 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 486 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_right (literal (valuationOf q) (486)) (literal (valuationOf q) (488)) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count487 q) 2 (meaning486 q) (meaning488 q) hs
  change valuationOf q 486 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 486 = false ∨ valuation q 488 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 485 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_two (literal (valuationOf q) (365)) (literal (valuationOf q) (485)) (literal (valuationOf q) (488)) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count487 q) 1 1 (meaning365 q) (meaning485 q) (meaning488 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 485 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 485 = false ∨ valuation q 488 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 366 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246])
  have hm := merge_left (literal (valuationOf q) (366)) (literal (valuationOf q) (488)) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]) (count487 q) 2 (meaning366 q) (meaning488 q) hs
  change valuationOf q 366 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 366 = false ∨ valuation q 488 = true := counterClause919 (baseVal q)

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 488 = false := by
  rw [value488]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count487 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause921 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 4 = true ∨ valuationOf q 834 = true := by
  have hs : count833 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-4)) (literal (valuationOf q) (834)) (countLit q [-3]) (countLit q [-4]) (count833 q) 1 1 (meaningNeg3 q) (meaningNeg4 q) (meaning834 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 4)) = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 4 = true ∨ valuation q 834 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 834 = false ∨ valuationOf q 836 = true := by
  have hs : count835 q = (countLit q [-1]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -4])
  have hm := merge_right (literal (valuationOf q) (834)) (literal (valuationOf q) (836)) (countLit q [-1]) (countLit q [-3, -4]) (count835 q) 2 (meaning834 q) (meaning836 q) hs
  change valuationOf q 834 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 834 = false ∨ valuation q 836 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 834 = false ∨ valuationOf q 837 = true := by
  have hs : count835 q = (countLit q [-1]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -4])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (834)) (literal (valuationOf q) (837)) (countLit q [-1]) (countLit q [-3, -4]) (count835 q) 1 2 (meaningNeg1 q) (meaning834 q) (meaning837 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 834 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 834 = false ∨ valuation q 837 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 838 = true := by
  have hs : count838 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (838)) (countLit q [-6]) (countLit q [-7]) (count838 q) 1 (meaningNeg7 q) (meaning838 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 838 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 838 = true := by
  have hs : count838 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (838)) (countLit q [-6]) (countLit q [-7]) (count838 q) 1 (meaningNeg6 q) (meaning838 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 838 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 7 = true ∨ valuationOf q 839 = true := by
  have hs : count838 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (839)) (countLit q [-6]) (countLit q [-7]) (count838 q) 1 1 (meaningNeg6 q) (meaningNeg7 q) (meaning839 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 839 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 840 = true := by
  have hs : count840 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (840)) (countLit q [-8]) (countLit q [-10]) (count840 q) 1 (meaningNeg10 q) (meaning840 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 840 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 840 = true := by
  have hs : count840 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (840)) (countLit q [-8]) (countLit q [-10]) (count840 q) 1 (meaningNeg8 q) (meaning840 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 840 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E097.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112097
