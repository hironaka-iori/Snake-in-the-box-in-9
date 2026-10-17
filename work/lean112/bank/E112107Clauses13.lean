import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (431)) (literal (valuationOf q) (433)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 1 (meaning431 q) (meaning433 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 433 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 432 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (432)) (literal (valuationOf q) (434)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 2 (meaning432 q) (meaning434 q) hs
  change valuationOf q 432 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 432 = false ∨ valuation q 434 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (433)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 1 (meaning377 q) (meaning433 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 433 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_two (literal (valuationOf q) (377)) (literal (valuationOf q) (431)) (literal (valuationOf q) (434)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 1 1 (meaning377 q) (meaning431 q) (meaning434 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 431 = false ∨ valuation q 434 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (378)) (literal (valuationOf q) (434)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 2 (meaning378 q) (meaning434 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 434 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 434 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (434)) (literal (valuationOf q) (436)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count435 q) 2 (meaning434 q) (meaning436 q) hs
  change valuationOf q 434 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 434 = false ∨ valuation q 436 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_two (literal (valuationOf q) (325)) (literal (valuationOf q) (433)) (literal (valuationOf q) (436)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count435 q) 1 1 (meaning325 q) (meaning433 q) (meaning436 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 433 = false ∨ valuation q 436 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 326 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (326)) (literal (valuationOf q) (436)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count435 q) 2 (meaning326 q) (meaning436 q) hs
  change valuationOf q 326 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 326 = false ∨ valuation q 436 = true := counterClause424 (baseVal q)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 436 = false := by
  rw [value436]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count435 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause426 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1325 = true := by
  have hs : count1325 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (1325)) (countLit q [-6]) (countLit q [-9]) (count1325 q) 1 (meaningNeg9 q) (meaning1325 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1325 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1325 = true := by
  have hs : count1325 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1325)) (countLit q [-6]) (countLit q [-9]) (count1325 q) 1 (meaningNeg6 q) (meaning1325 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1325 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 9 = true ∨ valuationOf q 1326 = true := by
  have hs : count1325 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (1326)) (countLit q [-6]) (countLit q [-9]) (count1325 q) 1 1 (meaningNeg6 q) (meaningNeg9 q) (meaning1326 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 9 = true ∨ valuation q 1326 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 1325 = false ∨ valuationOf q 1327 = true := by
  have hs : count1327 q = (countLit q [-4]) + (countLit q [-6, -9]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6, -9])
  have hm := merge_right (literal (valuationOf q) (1325)) (literal (valuationOf q) (1327)) (countLit q [-4]) (countLit q [-6, -9]) (count1327 q) 1 (meaning1325 q) (meaning1327 q) hs
  change valuationOf q 1325 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 1325 = false ∨ valuation q 1327 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-4]) + (countLit q [-6, -9]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6, -9])
  have hm := merge_right (literal (valuationOf q) (1326)) (literal (valuationOf q) (1328)) (countLit q [-4]) (countLit q [-6, -9]) (count1327 q) 2 (meaning1326 q) (meaning1328 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1328 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1327 = true := by
  have hs : count1327 q = (countLit q [-4]) + (countLit q [-6, -9]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6, -9])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1327)) (countLit q [-4]) (countLit q [-6, -9]) (count1327 q) 1 (meaningNeg4 q) (meaning1327 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1327 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1325 = false ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-4]) + (countLit q [-6, -9]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6, -9])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (1325)) (literal (valuationOf q) (1328)) (countLit q [-4]) (countLit q [-6, -9]) (count1327 q) 1 1 (meaningNeg4 q) (meaning1325 q) (meaning1328 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1325 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1325 = false ∨ valuation q 1328 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1326 = false ∨ valuationOf q 1329 = true := by
  have hs : count1327 q = (countLit q [-4]) + (countLit q [-6, -9]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6, -9])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (1326)) (literal (valuationOf q) (1329)) (countLit q [-4]) (countLit q [-6, -9]) (count1327 q) 1 2 (meaningNeg4 q) (meaning1326 q) (meaning1329 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1326 = false ∨ valuation q 1329 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-11]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-15])
  have hm := merge_right (literal (valuationOf q) (-15)) (literal (valuationOf q) (1330)) (countLit q [-11]) (countLit q [-15]) (count1330 q) 1 (meaningNeg15 q) (meaning1330 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1330 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-11]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1330)) (countLit q [-11]) (countLit q [-15]) (count1330 q) 1 (meaningNeg11 q) (meaning1330 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1330 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 15 = true ∨ valuationOf q 1331 = true := by
  have hs : count1330 q = (countLit q [-11]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (1331)) (countLit q [-11]) (countLit q [-15]) (count1330 q) 1 1 (meaningNeg11 q) (meaningNeg15 q) (meaning1331 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 15 = true ∨ valuation q 1331 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1332 = true := by
  have hs : count1332 q = (countLit q [-10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11, -15])
  have hm := merge_right (literal (valuationOf q) (1330)) (literal (valuationOf q) (1332)) (countLit q [-10]) (countLit q [-11, -15]) (count1332 q) 1 (meaning1330 q) (meaning1332 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1332 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1333 = true := by
  have hs : count1332 q = (countLit q [-10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11, -15])
  have hm := merge_right (literal (valuationOf q) (1331)) (literal (valuationOf q) (1333)) (countLit q [-10]) (countLit q [-11, -15]) (count1332 q) 2 (meaning1331 q) (meaning1333 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1333 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1332 = true := by
  have hs : count1332 q = (countLit q [-10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11, -15])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1332)) (countLit q [-10]) (countLit q [-11, -15]) (count1332 q) 1 (meaningNeg10 q) (meaning1332 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1332 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1330 = false ∨ valuationOf q 1333 = true := by
  have hs : count1332 q = (countLit q [-10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11, -15])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1333)) (countLit q [-10]) (countLit q [-11, -15]) (count1332 q) 1 1 (meaningNeg10 q) (meaning1330 q) (meaning1333 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1330 = false ∨ valuation q 1333 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1331 = false ∨ valuationOf q 1334 = true := by
  have hs : count1332 q = (countLit q [-10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11, -15])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (1331)) (literal (valuationOf q) (1334)) (countLit q [-10]) (countLit q [-11, -15]) (count1332 q) 1 2 (meaningNeg10 q) (meaning1331 q) (meaning1334 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1331 = false ∨ valuation q 1334 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1335 = true := by
  have hs : count1335 q = (countLit q [-4, -6, -9]) + (countLit q [-10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9]) (l₂ := [-10, -11, -15])
  have hm := merge_right (literal (valuationOf q) (1332)) (literal (valuationOf q) (1335)) (countLit q [-4, -6, -9]) (countLit q [-10, -11, -15]) (count1335 q) 1 (meaning1332 q) (meaning1335 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1335 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1336 = true := by
  have hs : count1335 q = (countLit q [-4, -6, -9]) + (countLit q [-10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9]) (l₂ := [-10, -11, -15])
  have hm := merge_right (literal (valuationOf q) (1333)) (literal (valuationOf q) (1336)) (countLit q [-4, -6, -9]) (countLit q [-10, -11, -15]) (count1335 q) 2 (meaning1333 q) (meaning1336 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1336 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1335 = true := by
  have hs : count1335 q = (countLit q [-4, -6, -9]) + (countLit q [-10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9]) (l₂ := [-10, -11, -15])
  have hm := merge_left (literal (valuationOf q) (1327)) (literal (valuationOf q) (1335)) (countLit q [-4, -6, -9]) (countLit q [-10, -11, -15]) (count1335 q) 1 (meaning1327 q) (meaning1335 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1335 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1336 = true := by
  have hs : count1335 q = (countLit q [-4, -6, -9]) + (countLit q [-10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9]) (l₂ := [-10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1332)) (literal (valuationOf q) (1336)) (countLit q [-4, -6, -9]) (countLit q [-10, -11, -15]) (count1335 q) 1 1 (meaning1327 q) (meaning1332 q) (meaning1336 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1332 = false ∨ valuation q 1336 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1337 = true := by
  have hs : count1335 q = (countLit q [-4, -6, -9]) + (countLit q [-10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9]) (l₂ := [-10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1333)) (literal (valuationOf q) (1337)) (countLit q [-4, -6, -9]) (countLit q [-10, -11, -15]) (count1335 q) 1 2 (meaning1327 q) (meaning1333 q) (meaning1337 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1333 = false ∨ valuation q 1337 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1338 = true := by
  have hs : count1335 q = (countLit q [-4, -6, -9]) + (countLit q [-10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9]) (l₂ := [-10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1334)) (literal (valuationOf q) (1338)) (countLit q [-4, -6, -9]) (countLit q [-10, -11, -15]) (count1335 q) 1 3 (meaning1327 q) (meaning1334 q) (meaning1338 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1334 = false ∨ valuation q 1338 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1336 = true := by
  have hs : count1335 q = (countLit q [-4, -6, -9]) + (countLit q [-10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9]) (l₂ := [-10, -11, -15])
  have hm := merge_left (literal (valuationOf q) (1328)) (literal (valuationOf q) (1336)) (countLit q [-4, -6, -9]) (countLit q [-10, -11, -15]) (count1335 q) 2 (meaning1328 q) (meaning1336 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1336 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E107.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112107
