import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (461)) (literal (valuationOf q) (463)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 1 (meaning461 q) (meaning463 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 463 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 462 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (462)) (literal (valuationOf q) (464)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 2 (meaning462 q) (meaning464 q) hs
  change valuationOf q 462 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 462 = false ∨ valuation q 464 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (433)) (literal (valuationOf q) (463)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 1 (meaning433 q) (meaning463 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 463 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (433)) (literal (valuationOf q) (461)) (literal (valuationOf q) (464)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 1 1 (meaning433 q) (meaning461 q) (meaning464 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 461 = false ∨ valuation q 464 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (463)) (literal (valuationOf q) (465)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 (meaning463 q) (meaning465 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 465 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 464 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (464)) (literal (valuationOf q) (466)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 2 (meaning464 q) (meaning466 q) hs
  change valuationOf q 464 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 464 = false ∨ valuation q 466 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (465)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 (meaning405 q) (meaning465 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 465 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 466 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (466)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 2 (meaning466 q) (meaning468 q) hs
  change valuationOf q 466 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 466 = false ∨ valuation q 468 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (349)) (literal (valuationOf q) (465)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 1 1 (meaning349 q) (meaning465 q) (meaning468 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 465 = false ∨ valuation q 468 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 350 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (350)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 2 (meaning350 q) (meaning468 q) hs
  change valuationOf q 350 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 350 = false ∨ valuation q 468 = true := counterClause586 (baseVal q)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 468 = false := by
  rw [value468]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count467 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause588 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1413 = true := by
  have hs : count1413 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (1413)) (countLit q [-4]) (countLit q [-6]) (count1413 q) 1 (meaningNeg6 q) (meaning1413 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1413 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 6 = true ∨ valuationOf q 1414 = true := by
  have hs : count1413 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-6)) (literal (valuationOf q) (1414)) (countLit q [-4]) (countLit q [-6]) (count1413 q) 1 1 (meaningNeg4 q) (meaningNeg6 q) (meaning1414 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 6)) = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 6 = true ∨ valuation q 1414 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1415 = true := by
  have hs : count1415 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_right (literal (valuationOf q) (1413)) (literal (valuationOf q) (1415)) (countLit q [-3]) (countLit q [-4, -6]) (count1415 q) 1 (meaning1413 q) (meaning1415 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1415 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1416 = true := by
  have hs : count1415 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_right (literal (valuationOf q) (1414)) (literal (valuationOf q) (1416)) (countLit q [-3]) (countLit q [-4, -6]) (count1415 q) 2 (meaning1414 q) (meaning1416 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1416 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1413 = false ∨ valuationOf q 1416 = true := by
  have hs : count1415 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1416)) (countLit q [-3]) (countLit q [-4, -6]) (count1415 q) 1 1 (meaningNeg3 q) (meaning1413 q) (meaning1416 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1413 = false ∨ valuation q 1416 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1414 = false ∨ valuationOf q 1417 = true := by
  have hs : count1415 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1417)) (countLit q [-3]) (countLit q [-4, -6]) (count1415 q) 1 2 (meaningNeg3 q) (meaning1414 q) (meaning1417 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1414 = false ∨ valuation q 1417 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (1418)) (countLit q [-8]) (countLit q [-10]) (count1418 q) 1 (meaningNeg10 q) (meaning1418 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1418 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1418)) (countLit q [-8]) (countLit q [-10]) (count1418 q) 1 (meaningNeg8 q) (meaning1418 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1418 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 10 = true ∨ valuationOf q 1419 = true := by
  have hs : count1418 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (1419)) (countLit q [-8]) (countLit q [-10]) (count1418 q) 1 1 (meaningNeg8 q) (meaningNeg10 q) (meaning1419 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 10 = true ∨ valuation q 1419 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1420 = true := by
  have hs : count1420 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1420)) (countLit q [-12]) (countLit q [-13]) (count1420 q) 1 (meaningNeg13 q) (meaning1420 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1420 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1420 = true := by
  have hs : count1420 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (1420)) (countLit q [-12]) (countLit q [-13]) (count1420 q) 1 (meaningNeg12 q) (meaning1420 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1420 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1421 = true := by
  have hs : count1420 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1421)) (countLit q [-12]) (countLit q [-13]) (count1420 q) 1 1 (meaningNeg12 q) (meaningNeg13 q) (meaning1421 q) hs
  change (! (valuationOf q 12)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 1421 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1420)) (literal (valuationOf q) (1422)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1422 q) 1 (meaning1420 q) (meaning1422 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1422 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1421)) (literal (valuationOf q) (1423)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1422 q) 2 (meaning1421 q) (meaning1423 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1423 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuationOf q) (1418)) (literal (valuationOf q) (1422)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1422 q) 1 (meaning1418 q) (meaning1422 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1422 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1423)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1422 q) 1 1 (meaning1418 q) (meaning1420 q) (meaning1423 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1420 = false ∨ valuation q 1423 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuationOf q) (1419)) (literal (valuationOf q) (1423)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1422 q) 2 (meaning1419 q) (meaning1423 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1423 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1415)) (literal (valuationOf q) (1426)) (countLit q [-3, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1426 q) 1 (meaning1415 q) (meaning1426 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1426 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true := by
  have hs : count1426 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1427)) (countLit q [-3, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1426 q) 1 1 (meaning1415 q) (meaning1422 q) (meaning1427 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1422 = false ∨ valuation q 1427 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1428 = true := by
  have hs : count1426 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1428)) (countLit q [-3, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1426 q) 1 2 (meaning1415 q) (meaning1423 q) (meaning1428 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1423 = false ∨ valuation q 1428 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1428 = true := by
  have hs : count1426 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1428)) (countLit q [-3, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1426 q) 2 1 (meaning1416 q) (meaning1422 q) (meaning1428 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1422 = false ∨ valuation q 1428 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E096.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112096
