import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 206 = false := by
  rw [value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (424 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 208 = false := by
  rw [value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (427 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 210 = false := by
  rw [value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (430 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 213 = false := by
  rw [value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (435 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 218 = false := by
  rw [value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (441 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 221 = false := by
  rw [value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (447 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 222 = false := by
  rw [value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (480 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 224 = false := by
  rw [value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (485 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 229 = false := by
  rw [value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (495 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 231 = false := by
  rw [value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (497 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 232 = false := by
  rw [value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (498 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 237 = false := by
  rw [value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (509 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 238 = false := by
  rw [value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (510 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause430 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [121]) + (countLit q [122]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122])
  have hm := merge_left (literal (valuationOf q) (121)) (literal (valuationOf q) (239)) (countLit q [121]) (countLit q [122]) (count239 q) 1 (meaning121 q) (meaning239 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 239 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (countLit q [120]) (countLit q [121, 122]) (count241 q) 1 (meaning239 q) (meaning241 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [123]) + (countLit q [124]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124])
  have hm := merge_left (literal (valuationOf q) (123)) (literal (valuationOf q) (243)) (countLit q [123]) (countLit q [124]) (count243 q) 1 (meaning123 q) (meaning243 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 243 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [123, 124]) + (countLit q [125, 126]) := List.countP_append (p := literal q) (l₁ := [123, 124]) (l₂ := [125, 126])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (247)) (countLit q [123, 124]) (countLit q [125, 126]) (count247 q) 1 (meaning243 q) (meaning247 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 247 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [120, 121, 122]) + (countLit q [123, 124, 125, 126]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122]) (l₂ := [123, 124, 125, 126])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (countLit q [120, 121, 122]) (countLit q [123, 124, 125, 126]) (count249 q) 1 (meaning247 q) (meaning249 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [120, 121, 122]) + (countLit q [123, 124, 125, 126]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122]) (l₂ := [123, 124, 125, 126])
  have hm := merge_left (literal (valuationOf q) (241)) (literal (valuationOf q) (249)) (countLit q [120, 121, 122]) (countLit q [123, 124, 125, 126]) (count249 q) 1 (meaning241 q) (meaning249 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 249 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_right (literal (valuationOf q) (129)) (literal (valuationOf q) (251)) (countLit q [128]) (countLit q [129]) (count251 q) 1 (meaning129 q) (meaning251 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 251 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128, 129])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [127]) (countLit q [128, 129]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_left (literal (valuationOf q) (132)) (literal (valuationOf q) (257)) (countLit q [132]) (countLit q [133]) (count257 q) 1 (meaning132 q) (meaning257 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 257 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [130, 131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [130, 131]) (l₂ := [132, 133])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [130, 131]) (countLit q [132, 133]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [127, 128, 129]) + (countLit q [130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129]) (l₂ := [130, 131, 132, 133])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [127, 128, 129]) (countLit q [130, 131, 132, 133]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [127, 128, 129]) + (countLit q [130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129]) (l₂ := [130, 131, 132, 133])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (261)) (countLit q [127, 128, 129]) (countLit q [130, 131, 132, 133]) (count261 q) 1 (meaning253 q) (meaning261 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 261 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [120, 121, 122, 123, 124, 125, 126]) + (countLit q [127, 128, 129, 130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126]) (l₂ := [127, 128, 129, 130, 131, 132, 133])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [120, 121, 122, 123, 124, 125, 126]) (countLit q [127, 128, 129, 130, 131, 132, 133]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [120, 121, 122, 123, 124, 125, 126]) + (countLit q [127, 128, 129, 130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126]) (l₂ := [127, 128, 129, 130, 131, 132, 133])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (263)) (countLit q [120, 121, 122, 123, 124, 125, 126]) (countLit q [127, 128, 129, 130, 131, 132, 133]) (count263 q) 1 (meaning249 q) (meaning263 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 263 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_right (literal (valuationOf q) (136)) (literal (valuationOf q) (265)) (countLit q [135]) (countLit q [136]) (count265 q) 1 (meaning136 q) (meaning265 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 265 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135, 136])
  have hm := merge_right (literal (valuationOf q) (265)) (literal (valuationOf q) (267)) (countLit q [134]) (countLit q [135, 136]) (count267 q) 1 (meaning265 q) (meaning267 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 267 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_right (literal (valuationOf q) (140)) (literal (valuationOf q) (271)) (countLit q [139]) (countLit q [140]) (count271 q) 1 (meaning140 q) (meaning271 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 271 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [137, 138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [137, 138]) (l₂ := [139, 140])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [137, 138]) (countLit q [139, 140]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [134, 135, 136]) + (countLit q [137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136]) (l₂ := [137, 138, 139, 140])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [134, 135, 136]) (countLit q [137, 138, 139, 140]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E187.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112187
