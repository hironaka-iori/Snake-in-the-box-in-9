import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 400 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (400)) (literal (valuationOf q) (428)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count427 q) 2 (meaning400 q) (meaning428 q) hs
  change valuationOf q 400 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 400 = false ∨ valuation q 428 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 428 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (428)) (literal (valuationOf q) (430)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 2 (meaning428 q) (meaning430 q) hs
  change valuationOf q 428 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 428 = false ∨ valuation q 430 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (375)) (literal (valuationOf q) (429)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 1 (meaning375 q) (meaning429 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 429 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 427 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_two (literal (valuationOf q) (375)) (literal (valuationOf q) (427)) (literal (valuationOf q) (430)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 1 1 (meaning375 q) (meaning427 q) (meaning430 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 427 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 427 = false ∨ valuation q 430 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 376 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (376)) (literal (valuationOf q) (430)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 2 (meaning376 q) (meaning430 q) hs
  change valuationOf q 376 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 376 = false ∨ valuation q 430 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 430 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (430)) (literal (valuationOf q) (432)) (countLit q [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count431 q) 2 (meaning430 q) (meaning432 q) hs
  change valuationOf q 430 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 430 = false ∨ valuation q 432 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (429)) (literal (valuationOf q) (432)) (countLit q [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count431 q) 1 1 (meaning323 q) (meaning429 q) (meaning432 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 429 = false ∨ valuation q 432 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 324 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (324)) (literal (valuationOf q) (432)) (countLit q [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count431 q) 2 (meaning324 q) (meaning432 q) hs
  change valuationOf q 324 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 324 = false ∨ valuation q 432 = true := counterClause425 (baseVal q)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 432 = false := by
  rw [value432]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count431 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause427 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1293)) (countLit q [-3]) (countLit q [-4, -5]) (count1293 q) 1 (meaningNeg3 q) (meaning1293 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1293 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1296 = true := by
  have hs : count1296 q = (countLit q [-9]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1296)) (countLit q [-9]) (countLit q [-13]) (count1296 q) 1 (meaningNeg13 q) (meaning1296 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1296 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1296 = true := by
  have hs : count1296 q = (countLit q [-9]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (1296)) (countLit q [-9]) (countLit q [-13]) (count1296 q) 1 (meaningNeg9 q) (meaning1296 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1296 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1298 = true := by
  have hs : count1298 q = (countLit q [-8]) + (countLit q [-9, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -13])
  have hm := merge_right (literal (valuationOf q) (1296)) (literal (valuationOf q) (1298)) (countLit q [-8]) (countLit q [-9, -13]) (count1298 q) 1 (meaning1296 q) (meaning1298 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1298 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 1298 = false ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -13])
  have hm := merge_right (literal (valuationOf q) (1298)) (literal (valuationOf q) (1301)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -13]) (count1301 q) 1 (meaning1298 q) (meaning1301 q) hs
  change valuationOf q 1298 = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 1298 = false ∨ valuation q 1301 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -13])
  have hm := merge_left (literal (valuationOf q) (1293)) (literal (valuationOf q) (1301)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -13]) (count1301 q) 1 (meaning1293 q) (meaning1301 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1301 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1302 = true := by
  have hs : count1301 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -13])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1298)) (literal (valuationOf q) (1302)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -13]) (count1301 q) 1 1 (meaning1293 q) (meaning1298 q) (meaning1302 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1298 = false ∨ valuation q 1302 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1307 = true := by
  have hs : count1307 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1307)) (countLit q [-16]) (countLit q [-18]) (count1307 q) 1 (meaningNeg18 q) (meaning1307 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1307 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1307 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1307 = true := by
  have hs : count1307 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1307)) (countLit q [-16]) (countLit q [-18]) (count1307 q) 1 (meaningNeg16 q) (meaning1307 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1307 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1307 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 18 = true ∨ valuationOf q 1308 = true := by
  have hs : count1307 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (1308)) (countLit q [-16]) (countLit q [-18]) (count1307 q) 1 1 (meaningNeg16 q) (meaningNeg18 q) (meaning1308 q) hs
  change (! (valuationOf q 16)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 1308 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 1307 = false ∨ valuationOf q 1309 = true := by
  have hs : count1309 q = (countLit q [-14]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -18])
  have hm := merge_right (literal (valuationOf q) (1307)) (literal (valuationOf q) (1309)) (countLit q [-14]) (countLit q [-16, -18]) (count1309 q) 1 (meaning1307 q) (meaning1309 q) hs
  change valuationOf q 1307 = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 1307 = false ∨ valuation q 1309 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1310 = true := by
  have hs : count1309 q = (countLit q [-14]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -18])
  have hm := merge_right (literal (valuationOf q) (1308)) (literal (valuationOf q) (1310)) (countLit q [-14]) (countLit q [-16, -18]) (count1309 q) 2 (meaning1308 q) (meaning1310 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1310 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1309 = true := by
  have hs : count1309 q = (countLit q [-14]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -18])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1309)) (countLit q [-14]) (countLit q [-16, -18]) (count1309 q) 1 (meaningNeg14 q) (meaning1309 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1309 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1307 = false ∨ valuationOf q 1310 = true := by
  have hs : count1309 q = (countLit q [-14]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -18])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1307)) (literal (valuationOf q) (1310)) (countLit q [-14]) (countLit q [-16, -18]) (count1309 q) 1 1 (meaningNeg14 q) (meaning1307 q) (meaning1310 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1307 = false ∨ valuationOf q 1310 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1307 = false ∨ valuation q 1310 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1308 = false ∨ valuationOf q 1311 = true := by
  have hs : count1309 q = (countLit q [-14]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -18])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1308)) (literal (valuationOf q) (1311)) (countLit q [-14]) (countLit q [-16, -18]) (count1309 q) 1 2 (meaningNeg14 q) (meaning1308 q) (meaning1311 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1308 = false ∨ valuation q 1311 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1312 = true := by
  have hs : count1312 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1312)) (countLit q [-20]) (countLit q [-22]) (count1312 q) 1 (meaningNeg22 q) (meaning1312 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1312 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1312 = true := by
  have hs : count1312 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1312)) (countLit q [-20]) (countLit q [-22]) (count1312 q) 1 (meaningNeg20 q) (meaning1312 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1312 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1313 = true := by
  have hs : count1312 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1313)) (countLit q [-20]) (countLit q [-22]) (count1312 q) 1 1 (meaningNeg20 q) (meaningNeg22 q) (meaning1313 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 1313 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1314 = true := by
  have hs : count1314 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1314)) (countLit q [-23]) (countLit q [-24]) (count1314 q) 1 (meaningNeg24 q) (meaning1314 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1314 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1314 = true := by
  have hs : count1314 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (1314)) (countLit q [-23]) (countLit q [-24]) (count1314 q) 1 (meaningNeg23 q) (meaning1314 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1314 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1315 = true := by
  have hs : count1314 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-23)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1315)) (countLit q [-23]) (countLit q [-24]) (count1314 q) 1 1 (meaningNeg23 q) (meaningNeg24 q) (meaning1315 q) hs
  change (! (valuationOf q 23)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 24 = true ∨ valuation q 1315 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 1314 = false ∨ valuationOf q 1316 = true := by
  have hs : count1316 q = (countLit q [-20, -22]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-23, -24])
  have hm := merge_right (literal (valuationOf q) (1314)) (literal (valuationOf q) (1316)) (countLit q [-20, -22]) (countLit q [-23, -24]) (count1316 q) 1 (meaning1314 q) (meaning1316 q) hs
  change valuationOf q 1314 = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 1314 = false ∨ valuation q 1316 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E090.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112090
