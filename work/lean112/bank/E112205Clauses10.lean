import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [205, 206, 207, 208, 209, 210, 211]) + (countLit q [212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211]) (l₂ := [212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (411)) (literal (valuationOf q) (425)) (countLit q [205, 206, 207, 208, 209, 210, 211]) (countLit q [212, 213, 214, 215, 216, 217, 218]) (count425 q) 1 (meaning411 q) (meaning425 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 425 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 423 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [205, 206, 207, 208, 209, 210, 211]) + (countLit q [212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211]) (l₂ := [212, 213, 214, 215, 216, 217, 218])
  have hm := merge_two (literal (valuationOf q) (411)) (literal (valuationOf q) (423)) (literal (valuationOf q) (426)) (countLit q [205, 206, 207, 208, 209, 210, 211]) (countLit q [212, 213, 214, 215, 216, 217, 218]) (count425 q) 1 1 (meaning411 q) (meaning423 q) (meaning426 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 423 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 423 = false ∨ valuation q 426 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 412 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [205, 206, 207, 208, 209, 210, 211]) + (countLit q [212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211]) (l₂ := [212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (412)) (literal (valuationOf q) (426)) (countLit q [205, 206, 207, 208, 209, 210, 211]) (countLit q [212, 213, 214, 215, 216, 217, 218]) (count425 q) 2 (meaning412 q) (meaning426 q) hs
  change valuationOf q 412 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 412 = false ∨ valuation q 426 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 426 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (426)) (literal (valuationOf q) (428)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count427 q) 2 (meaning426 q) (meaning428 q) hs
  change valuationOf q 426 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 426 = false ∨ valuation q 428 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (399)) (literal (valuationOf q) (427)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count427 q) 1 (meaning399 q) (meaning427 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 427 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_two (literal (valuationOf q) (399)) (literal (valuationOf q) (425)) (literal (valuationOf q) (428)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count427 q) 1 1 (meaning399 q) (meaning425 q) (meaning428 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 425 = false ∨ valuation q 428 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 400 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (400)) (literal (valuationOf q) (428)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count427 q) 2 (meaning400 q) (meaning428 q) hs
  change valuationOf q 400 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 400 = false ∨ valuation q 428 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 428 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (428)) (literal (valuationOf q) (430)) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 2 (meaning428 q) (meaning430 q) hs
  change valuationOf q 428 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 428 = false ∨ valuation q 430 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (375)) (literal (valuationOf q) (429)) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 1 (meaning375 q) (meaning429 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 429 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 427 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_two (literal (valuationOf q) (375)) (literal (valuationOf q) (427)) (literal (valuationOf q) (430)) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 1 1 (meaning375 q) (meaning427 q) (meaning430 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 427 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 427 = false ∨ valuation q 430 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 376 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (376)) (literal (valuationOf q) (430)) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 2 (meaning376 q) (meaning430 q) hs
  change valuationOf q 376 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 376 = false ∨ valuation q 430 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 430 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (430)) (literal (valuationOf q) (432)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count431 q) 2 (meaning430 q) (meaning432 q) hs
  change valuationOf q 430 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 430 = false ∨ valuation q 432 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (429)) (literal (valuationOf q) (432)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count431 q) 1 1 (meaning323 q) (meaning429 q) (meaning432 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 429 = false ∨ valuation q 432 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 324 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (324)) (literal (valuationOf q) (432)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count431 q) 2 (meaning324 q) (meaning432 q) hs
  change valuationOf q 324 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 324 = false ∨ valuation q 432 = true := counterClause336 (baseVal q)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 432 = false := by
  rw [value432]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count431 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause338 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1315 = true := by
  have hs : count1315 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1315)) (countLit q [-3]) (countLit q [-4]) (count1315 q) 1 (meaningNeg3 q) (meaning1315 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1315 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 4 = true ∨ valuationOf q 1316 = true := by
  have hs : count1315 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-4)) (literal (valuationOf q) (1316)) (countLit q [-3]) (countLit q [-4]) (count1315 q) 1 1 (meaningNeg3 q) (meaningNeg4 q) (meaning1316 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 4)) = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 4 = true ∨ valuation q 1316 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 1315 = false ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-2]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -4])
  have hm := merge_right (literal (valuationOf q) (1315)) (literal (valuationOf q) (1317)) (countLit q [-2]) (countLit q [-3, -4]) (count1317 q) 1 (meaning1315 q) (meaning1317 q) hs
  change valuationOf q 1315 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 1315 = false ∨ valuation q 1317 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 1316 = false ∨ valuationOf q 1318 = true := by
  have hs : count1317 q = (countLit q [-2]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -4])
  have hm := merge_right (literal (valuationOf q) (1316)) (literal (valuationOf q) (1318)) (countLit q [-2]) (countLit q [-3, -4]) (count1317 q) 2 (meaning1316 q) (meaning1318 q) hs
  change valuationOf q 1316 = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 1316 = false ∨ valuation q 1318 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-2]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -4])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1317)) (countLit q [-2]) (countLit q [-3, -4]) (count1317 q) 1 (meaningNeg2 q) (meaning1317 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1317 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1315 = false ∨ valuationOf q 1318 = true := by
  have hs : count1317 q = (countLit q [-2]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -4])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1315)) (literal (valuationOf q) (1318)) (countLit q [-2]) (countLit q [-3, -4]) (count1317 q) 1 1 (meaningNeg2 q) (meaning1315 q) (meaning1318 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1315 = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1315 = false ∨ valuation q 1318 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1316 = false ∨ valuationOf q 1319 = true := by
  have hs : count1317 q = (countLit q [-2]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -4])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1316)) (literal (valuationOf q) (1319)) (countLit q [-2]) (countLit q [-3, -4]) (count1317 q) 1 2 (meaningNeg2 q) (meaning1316 q) (meaning1319 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1316 = false ∨ valuation q 1319 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 10 = true ∨ valuationOf q 1321 = true := by
  have hs : count1320 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (1321)) (countLit q [-9]) (countLit q [-10]) (count1320 q) 1 1 (meaningNeg9 q) (meaningNeg10 q) (meaning1321 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 10 = true ∨ valuation q 1321 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-8]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -10])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1322)) (countLit q [-8]) (countLit q [-9, -10]) (count1322 q) 1 (meaningNeg8 q) (meaning1322 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1322 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1321 = false ∨ valuationOf q 1324 = true := by
  have hs : count1322 q = (countLit q [-8]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -10])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1324)) (countLit q [-8]) (countLit q [-9, -10]) (count1322 q) 1 2 (meaningNeg8 q) (meaning1321 q) (meaning1324 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1321 = false ∨ valuation q 1324 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1325 = true := by
  have hs : count1325 q = (countLit q [-2, -3, -4]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4]) (l₂ := [-8, -9, -10])
  have hm := merge_left (literal (valuationOf q) (1317)) (literal (valuationOf q) (1325)) (countLit q [-2, -3, -4]) (countLit q [-8, -9, -10]) (count1325 q) 1 (meaning1317 q) (meaning1325 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1325 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1326 = true := by
  have hs : count1325 q = (countLit q [-2, -3, -4]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4]) (l₂ := [-8, -9, -10])
  have hm := merge_two (literal (valuationOf q) (1317)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1326)) (countLit q [-2, -3, -4]) (countLit q [-8, -9, -10]) (count1325 q) 1 1 (meaning1317 q) (meaning1322 q) (meaning1326 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1322 = false ∨ valuation q 1326 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1328 = true := by
  have hs : count1325 q = (countLit q [-2, -3, -4]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4]) (l₂ := [-8, -9, -10])
  have hm := merge_two (literal (valuationOf q) (1317)) (literal (valuationOf q) (1324)) (literal (valuationOf q) (1328)) (countLit q [-2, -3, -4]) (countLit q [-8, -9, -10]) (count1325 q) 1 3 (meaning1317 q) (meaning1324 q) (meaning1328 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1324 = false ∨ valuation q 1328 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 1318 = false ∨ valuationOf q 1326 = true := by
  have hs : count1325 q = (countLit q [-2, -3, -4]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4]) (l₂ := [-8, -9, -10])
  have hm := merge_left (literal (valuationOf q) (1318)) (literal (valuationOf q) (1326)) (countLit q [-2, -3, -4]) (countLit q [-8, -9, -10]) (count1325 q) 2 (meaning1318 q) (meaning1326 q) hs
  change valuationOf q 1318 = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 1318 = false ∨ valuation q 1326 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1330 = true := by
  have hs : count1325 q = (countLit q [-2, -3, -4]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4]) (l₂ := [-8, -9, -10])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1324)) (literal (valuationOf q) (1330)) (countLit q [-2, -3, -4]) (countLit q [-8, -9, -10]) (count1325 q) 3 3 (meaning1319 q) (meaning1324 q) (meaning1330 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1324 = false ∨ valuation q 1330 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E205.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112205
