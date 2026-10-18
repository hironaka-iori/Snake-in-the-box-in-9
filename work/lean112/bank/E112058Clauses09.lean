import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 212 = false := by
  rw [value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (410 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 217 = false := by
  rw [value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (481 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 219 = false := by
  rw [value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (487 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 220 = false := by
  rw [value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (488 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 222 = false := by
  rw [value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (491 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 223 = false := by
  rw [value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (493 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 227 = false := by
  rw [value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (499 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 230 = false := by
  rw [value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (508 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause297 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [122]) + (countLit q [123]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123])
  have hm := merge_right (literal (valuationOf q) (123)) (literal (valuationOf q) (239)) (countLit q [122]) (countLit q [123]) (count239 q) 1 (meaning123 q) (meaning239 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 239 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [120, 121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [120, 121]) (l₂ := [122, 123])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (countLit q [120, 121]) (countLit q [122, 123]) (count241 q) 1 (meaning239 q) (meaning241 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (257)) (countLit q [117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 128, 129, 130, 131]) (count257 q) 1 (meaning243 q) (meaning257 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 257 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (285)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (count285 q) 1 (meaning257 q) (meaning285 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 285 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (343)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 (meaning285 q) (meaning343 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 343 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [180]) + (countLit q [181]) := List.countP_append (p := literal q) (l₁ := [180]) (l₂ := [181])
  have hm := merge_right (literal (valuationOf q) (181)) (literal (valuationOf q) (351)) (countLit q [180]) (countLit q [181]) (count351 q) 1 (meaning181 q) (meaning351 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 351 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [178, 179]) + (countLit q [180, 181]) := List.countP_append (p := literal q) (l₁ := [178, 179]) (l₂ := [180, 181])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [178, 179]) (countLit q [180, 181]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [175, 176, 177]) + (countLit q [178, 179, 180, 181]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177]) (l₂ := [178, 179, 180, 181])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [175, 176, 177]) (countLit q [178, 179, 180, 181]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [175, 176, 177, 178, 179, 180, 181]) + (countLit q [182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181]) (l₂ := [182, 183, 184, 185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (369)) (countLit q [175, 176, 177, 178, 179, 180, 181]) (countLit q [182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 (meaning355 q) (meaning369 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 369 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (383)) (countLit q [196]) (countLit q [197]) (count383 q) 1 (meaning196 q) (meaning383 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 383 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [196, 197]) + (countLit q [198, 199]) := List.countP_append (p := literal q) (l₁ := [196, 197]) (l₂ := [198, 199])
  have hm := merge_left (literal (valuationOf q) (383)) (literal (valuationOf q) (387)) (countLit q [196, 197]) (countLit q [198, 199]) (count387 q) 1 (meaning383 q) (meaning387 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 387 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [196, 197, 198, 199]) + (countLit q [200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199]) (l₂ := [200, 201, 202, 203])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (395)) (countLit q [196, 197, 198, 199]) (countLit q [200, 201, 202, 203]) (count395 q) 1 (meaning387 q) (meaning395 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 395 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_right (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_left (literal (valuationOf q) (369)) (literal (valuationOf q) (399)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 1 (meaning369 q) (meaning399 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 399 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) + (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (l₂ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (399)) (literal (valuationOf q) (457)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count457 q) 1 (meaning399 q) (meaning457 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 457 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (343)) (literal (valuationOf q) (457)) (literal (valuationOf q) (460)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count459 q) 1 1 (meaning343 q) (meaning457 q) (meaning460 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 457 = false ∨ valuation q 460 = true := counterClause314 (baseVal q)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 460 = false := by
  rw [value460]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count459 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause316 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1401 = true := by
  have hs : count1401 q = (countLit q [-5]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (1401)) (countLit q [-5]) (countLit q [-6]) (count1401 q) 1 (meaningNeg6 q) (meaning1401 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1401 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1401 = true := by
  have hs : count1401 q = (countLit q [-5]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-6])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (1401)) (countLit q [-5]) (countLit q [-6]) (count1401 q) 1 (meaningNeg5 q) (meaning1401 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1401 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 6 = true ∨ valuationOf q 1402 = true := by
  have hs : count1401 q = (countLit q [-5]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-6])
  have hm := merge_two (literal (valuationOf q) (-5)) (literal (valuationOf q) (-6)) (literal (valuationOf q) (1402)) (countLit q [-5]) (countLit q [-6]) (count1401 q) 1 1 (meaningNeg5 q) (meaningNeg6 q) (meaning1402 q) hs
  change (! (valuationOf q 5)) = false ∨ (! (valuationOf q 6)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 6 = true ∨ valuation q 1402 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-2]) + (countLit q [-5, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -6])
  have hm := merge_right (literal (valuationOf q) (1401)) (literal (valuationOf q) (1403)) (countLit q [-2]) (countLit q [-5, -6]) (count1403 q) 1 (meaning1401 q) (meaning1403 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1403 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1404 = true := by
  have hs : count1403 q = (countLit q [-2]) + (countLit q [-5, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -6])
  have hm := merge_right (literal (valuationOf q) (1402)) (literal (valuationOf q) (1404)) (countLit q [-2]) (countLit q [-5, -6]) (count1403 q) 2 (meaning1402 q) (meaning1404 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1404 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E058.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112058
