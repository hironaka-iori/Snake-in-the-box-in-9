import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [232, 233, 234, 235]) + (countLit q [236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [232, 233, 234, 235]) (l₂ := [236, 238, 239, 240])
  have hm := merge_two (literal (valuationOf q) (459)) (literal (valuationOf q) (465)) (literal (valuationOf q) (468)) (countLit q [232, 233, 234, 235]) (countLit q [236, 238, 239, 240]) (count467 q) 1 1 (meaning459 q) (meaning465 q) (meaning468 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 465 = false ∨ valuation q 468 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 460 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [232, 233, 234, 235]) + (countLit q [236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [232, 233, 234, 235]) (l₂ := [236, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (460)) (literal (valuationOf q) (468)) (countLit q [232, 233, 234, 235]) (countLit q [236, 238, 239, 240]) (count467 q) 2 (meaning460 q) (meaning468 q) hs
  change valuationOf q 460 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 460 = false ∨ valuation q 468 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [225, 226, 227, 228, 229, 230, 231]) + (countLit q [232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231]) (l₂ := [232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (467)) (literal (valuationOf q) (469)) (countLit q [225, 226, 227, 228, 229, 230, 231]) (countLit q [232, 233, 234, 235, 236, 238, 239, 240]) (count469 q) 1 (meaning467 q) (meaning469 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 469 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 468 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [225, 226, 227, 228, 229, 230, 231]) + (countLit q [232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231]) (l₂ := [232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (468)) (literal (valuationOf q) (470)) (countLit q [225, 226, 227, 228, 229, 230, 231]) (countLit q [232, 233, 234, 235, 236, 238, 239, 240]) (count469 q) 2 (meaning468 q) (meaning470 q) hs
  change valuationOf q 468 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 468 = false ∨ valuation q 470 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [225, 226, 227, 228, 229, 230, 231]) + (countLit q [232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231]) (l₂ := [232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (453)) (literal (valuationOf q) (469)) (countLit q [225, 226, 227, 228, 229, 230, 231]) (countLit q [232, 233, 234, 235, 236, 238, 239, 240]) (count469 q) 1 (meaning453 q) (meaning469 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 469 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (469)) (literal (valuationOf q) (471)) (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count471 q) 1 (meaning469 q) (meaning471 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 471 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 470 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (470)) (literal (valuationOf q) (472)) (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count471 q) 2 (meaning470 q) (meaning472 q) hs
  change valuationOf q 470 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 470 = false ∨ valuation q 472 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (441)) (literal (valuationOf q) (471)) (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count471 q) 1 (meaning441 q) (meaning471 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 471 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_two (literal (valuationOf q) (441)) (literal (valuationOf q) (469)) (literal (valuationOf q) (472)) (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count471 q) 1 1 (meaning441 q) (meaning469 q) (meaning472 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 469 = false ∨ valuation q 472 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 442 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (442)) (literal (valuationOf q) (472)) (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count471 q) 2 (meaning442 q) (meaning472 q) hs
  change valuationOf q 442 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 442 = false ∨ valuation q 472 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (471)) (literal (valuationOf q) (473)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count473 q) 1 (meaning471 q) (meaning473 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 473 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 472 = false ∨ valuationOf q 474 = true := by
  have hs : count473 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (472)) (literal (valuationOf q) (474)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count473 q) 2 (meaning472 q) (meaning474 q) hs
  change valuationOf q 472 = false ∨ valuationOf q 474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 472 = false ∨ valuation q 474 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (413)) (literal (valuationOf q) (473)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count473 q) 1 (meaning413 q) (meaning473 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 473 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 471 = false ∨ valuationOf q 474 = true := by
  have hs : count473 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_two (literal (valuationOf q) (413)) (literal (valuationOf q) (471)) (literal (valuationOf q) (474)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count473 q) 1 1 (meaning413 q) (meaning471 q) (meaning474 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 471 = false ∨ valuationOf q 474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 471 = false ∨ valuation q 474 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 414 = false ∨ valuationOf q 474 = true := by
  have hs : count473 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (414)) (literal (valuationOf q) (474)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count473 q) 2 (meaning414 q) (meaning474 q) hs
  change valuationOf q 414 = false ∨ valuationOf q 474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 414 = false ∨ valuation q 474 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 474 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) + (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (l₂ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (474)) (literal (valuationOf q) (476)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count475 q) 2 (meaning474 q) (meaning476 q) hs
  change valuationOf q 474 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 474 = false ∨ valuation q 476 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) + (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (l₂ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_two (literal (valuationOf q) (355)) (literal (valuationOf q) (473)) (literal (valuationOf q) (476)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count475 q) 1 1 (meaning355 q) (meaning473 q) (meaning476 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 473 = false ∨ valuation q 476 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 356 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) + (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (l₂ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (356)) (literal (valuationOf q) (476)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]) (count475 q) 2 (meaning356 q) (meaning476 q) hs
  change valuationOf q 356 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 356 = false ∨ valuation q 476 = true := counterClause882 (baseVal q)

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 476 = false := by
  rw [value476]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count475 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause884 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 809 = true := by
  have hs : count809 q = (countLit q [-2]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (809)) (countLit q [-2]) (countLit q [-5]) (count809 q) 1 (meaningNeg5 q) (meaning809 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 809 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 811 = true := by
  have hs : count811 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_right (literal (valuationOf q) (809)) (literal (valuationOf q) (811)) (countLit q [-1]) (countLit q [-2, -5]) (count811 q) 1 (meaning809 q) (meaning811 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 811 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 814 = true := by
  have hs : count814 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (814)) (countLit q [-8]) (countLit q [-10]) (count814 q) 1 (meaningNeg10 q) (meaning814 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 814 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 13 = true ∨ valuationOf q 817 = true := by
  have hs : count816 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (817)) (countLit q [-11]) (countLit q [-13]) (count816 q) 1 1 (meaningNeg11 q) (meaningNeg13 q) (meaning817 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 13 = true ∨ valuation q 817 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 817 = false ∨ valuationOf q 820 = true := by
  have hs : count818 q = (countLit q [-8, -10]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (814)) (literal (valuationOf q) (817)) (literal (valuationOf q) (820)) (countLit q [-8, -10]) (countLit q [-11, -13]) (count818 q) 1 2 (meaning814 q) (meaning817 q) (meaning820 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 817 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 817 = false ∨ valuation q 820 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 820 = false ∨ valuationOf q 825 = true := by
  have hs : count822 q = (countLit q [-1, -2, -5]) + (countLit q [-8, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-8, -10, -11, -13])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (820)) (literal (valuationOf q) (825)) (countLit q [-1, -2, -5]) (countLit q [-8, -10, -11, -13]) (count822 q) 1 3 (meaning811 q) (meaning820 q) (meaning825 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 820 = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 820 = false ∨ valuation q 825 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 834 = true := by
  have hs : count834 q = (countLit q [-20]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (834)) (countLit q [-20]) (countLit q [-23]) (count834 q) 1 (meaningNeg20 q) (meaning834 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 834 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 836 = true := by
  have hs : count836 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (836)) (countLit q [-25]) (countLit q [-27]) (count836 q) 1 (meaningNeg25 q) (meaning836 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 836 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 834 = false ∨ valuationOf q 836 = false ∨ valuationOf q 839 = true := by
  have hs : count838 q = (countLit q [-20, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-20, -23]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (834)) (literal (valuationOf q) (836)) (literal (valuationOf q) (839)) (countLit q [-20, -23]) (countLit q [-25, -27]) (count838 q) 1 1 (meaning834 q) (meaning836 q) (meaning839 q) hs
  change valuationOf q 834 = false ∨ valuationOf q 836 = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 834 = false ∨ valuation q 836 = false ∨ valuation q 839 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 843 = true := by
  have hs : count842 q = (countLit q [-14, -17, -19]) + (countLit q [-20, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19]) (l₂ := [-20, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (839)) (literal (valuationOf q) (843)) (countLit q [-14, -17, -19]) (countLit q [-20, -23, -25, -27]) (count842 q) 2 (meaning839 q) (meaning843 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 843 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 843 = false ∨ valuationOf q 854 = true := by
  have hs : count849 q = (countLit q [-1, -2, -5, -8, -10, -11, -13]) + (countLit q [-14, -17, -19, -20, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -11, -13]) (l₂ := [-14, -17, -19, -20, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (825)) (literal (valuationOf q) (843)) (literal (valuationOf q) (854)) (countLit q [-1, -2, -5, -8, -10, -11, -13]) (countLit q [-14, -17, -19, -20, -23, -25, -27]) (count849 q) 4 2 (meaning825 q) (meaning843 q) (meaning854 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 843 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 843 = false ∨ valuation q 854 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 863 = true := by
  have hs : count863 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (863)) (countLit q [-31]) (countLit q [-33]) (count863 q) 1 (meaningNeg31 q) (meaning863 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 863 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-29]) + (countLit q [-31, -33]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31, -33])
  have hm := merge_right (literal (valuationOf q) (863)) (literal (valuationOf q) (865)) (countLit q [-29]) (countLit q [-31, -33]) (count865 q) 1 (meaning863 q) (meaning865 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 865 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E040.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112040
