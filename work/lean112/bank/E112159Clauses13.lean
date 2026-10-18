import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 190 = false := by
  rw [value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (360 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 196 = false := by
  rw [value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (373 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 197 = false := by
  rw [value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (374 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 200 = false := by
  rw [value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (378 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 202 = false := by
  rw [value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (417 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 205 = false := by
  rw [value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (423 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 206 = false := by
  rw [value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (424 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 208 = false := by
  rw [value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (430 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 212 = false := by
  rw [value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (437 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 216 = false := by
  rw [value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (441 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 217 = false := by
  rw [value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (442 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 219 = false := by
  rw [value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (480 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 222 = false := by
  rw [value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (485 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 224 = false := by
  rw [value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (490 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 229 = false := by
  rw [value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (497 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 231 = false := by
  rw [value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (503 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 233 = false := by
  rw [value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (507 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 235 = false := by
  rw [value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (510 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause435 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_left (literal (valuationOf q) (120)) (literal (valuationOf q) (237)) (countLit q [120]) (countLit q [121]) (count237 q) 1 (meaning120 q) (meaning237 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 237 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120, 121])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [119]) (countLit q [120, 121]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [124]) + (countLit q [126]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [126])
  have hm := merge_left (literal (valuationOf q) (124)) (literal (valuationOf q) (243)) (countLit q [124]) (countLit q [126]) (count243 q) 1 (meaning124 q) (meaning243 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 243 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [122, 123]) + (countLit q [124, 126]) := List.countP_append (p := literal q) (l₁ := [122, 123]) (l₂ := [124, 126])
  have hm := merge_right (literal (valuationOf q) (243)) (literal (valuationOf q) (245)) (countLit q [122, 123]) (countLit q [124, 126]) (count245 q) 1 (meaning243 q) (meaning245 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 245 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [119, 120, 121]) + (countLit q [122, 123, 124, 126]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121]) (l₂ := [122, 123, 124, 126])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (247)) (countLit q [119, 120, 121]) (countLit q [122, 123, 124, 126]) (count247 q) 1 (meaning239 q) (meaning247 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 247 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 245 = false ∨ valuationOf q 248 = true := by
  have hs : count247 q = (countLit q [119, 120, 121]) + (countLit q [122, 123, 124, 126]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121]) (l₂ := [122, 123, 124, 126])
  have hm := merge_two (literal (valuationOf q) (239)) (literal (valuationOf q) (245)) (literal (valuationOf q) (248)) (countLit q [119, 120, 121]) (countLit q [122, 123, 124, 126]) (count247 q) 1 1 (meaning239 q) (meaning245 q) (meaning248 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 245 = false ∨ valuationOf q 248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 245 = false ∨ valuation q 248 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_right (literal (valuationOf q) (129)) (literal (valuationOf q) (249)) (countLit q [128]) (countLit q [129]) (count249 q) 1 (meaning129 q) (meaning249 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 249 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128, 129])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [127]) (countLit q [128, 129]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131])
  have hm := merge_right (literal (valuationOf q) (131)) (literal (valuationOf q) (253)) (countLit q [130]) (countLit q [131]) (count253 q) 1 (meaning131 q) (meaning253 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 253 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [130, 131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [130, 131]) (l₂ := [132, 133])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (257)) (countLit q [130, 131]) (countLit q [132, 133]) (count257 q) 1 (meaning253 q) (meaning257 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 257 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [127, 128, 129]) + (countLit q [130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129]) (l₂ := [130, 131, 132, 133])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [127, 128, 129]) (countLit q [130, 131, 132, 133]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [127, 128, 129]) + (countLit q [130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129]) (l₂ := [130, 131, 132, 133])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (259)) (countLit q [127, 128, 129]) (countLit q [130, 131, 132, 133]) (count259 q) 1 (meaning251 q) (meaning259 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 259 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 126]) + (countLit q [127, 128, 129, 130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 126]) (l₂ := [127, 128, 129, 130, 131, 132, 133])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (261)) (countLit q [119, 120, 121, 122, 123, 124, 126]) (countLit q [127, 128, 129, 130, 131, 132, 133]) (count261 q) 1 (meaning247 q) (meaning261 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 261 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 259 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 126]) + (countLit q [127, 128, 129, 130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 126]) (l₂ := [127, 128, 129, 130, 131, 132, 133])
  have hm := merge_two (literal (valuationOf q) (247)) (literal (valuationOf q) (259)) (literal (valuationOf q) (262)) (countLit q [119, 120, 121, 122, 123, 124, 126]) (countLit q [127, 128, 129, 130, 131, 132, 133]) (count261 q) 1 1 (meaning247 q) (meaning259 q) (meaning262 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 259 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 259 = false ∨ valuation q 262 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E159.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112159
