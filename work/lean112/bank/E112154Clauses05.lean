import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 168 = false := by
  rw [value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (367 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 170 = false := by
  rw [value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (376 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 173 = false := by
  rw [value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (419 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 177 = false := by
  rw [value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (425 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 179 = false := by
  rw [value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (431 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 180 = false := by
  rw [value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (434 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 181 = false := by
  rw [value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (436 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 184 = false := by
  rw [value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (440 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 188 = false := by
  rw [value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (451 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 189 = false := by
  rw [value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (454 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 194 = false := by
  rw [value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (463 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 195 = false := by
  rw [value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (466 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 196 = false := by
  rw [value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (468 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 199 = false := by
  rw [value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (472 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 202 = false := by
  rw [value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (477 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause176 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_right (literal (valuationOf q) (141)) (literal (valuationOf q) (273)) (countLit q [140]) (countLit q [141]) (count273 q) 1 (meaning141 q) (meaning273 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 273 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [139]) + (countLit q [140, 141]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140, 141])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [139]) (countLit q [140, 141]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144])
  have hm := merge_right (literal (valuationOf q) (144)) (literal (valuationOf q) (277)) (countLit q [143]) (countLit q [144]) (count277 q) 1 (meaning144 q) (meaning277 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 277 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [142]) + (countLit q [143, 144]) := List.countP_append (p := literal q) (l₁ := [142]) (l₂ := [143, 144])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [142]) (countLit q [143, 144]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [139, 140, 141]) + (countLit q [142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141]) (l₂ := [142, 143, 144])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (281)) (countLit q [139, 140, 141]) (countLit q [142, 143, 144]) (count281 q) 1 (meaning275 q) (meaning281 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 281 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [139, 140, 141]) + (countLit q [142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141]) (l₂ := [142, 143, 144])
  have hm := merge_two (literal (valuationOf q) (275)) (literal (valuationOf q) (279)) (literal (valuationOf q) (282)) (countLit q [139, 140, 141]) (countLit q [142, 143, 144]) (count281 q) 1 1 (meaning275 q) (meaning279 q) (meaning282 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 279 = false ∨ valuation q 282 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_left (literal (valuationOf q) (150)) (literal (valuationOf q) (289)) (countLit q [150]) (countLit q [151]) (count289 q) 1 (meaning150 q) (meaning289 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 289 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [148, 149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [148, 149]) (l₂ := [150, 151])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [148, 149]) (countLit q [150, 151]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [145, 146, 147]) + (countLit q [148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147]) (l₂ := [148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [145, 146, 147]) (countLit q [148, 149, 150, 151]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (295)) (countLit q [139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151]) (count295 q) 1 (meaning281 q) (meaning295 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 295 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 282 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151])
  have hm := merge_left (literal (valuationOf q) (282)) (literal (valuationOf q) (296)) (countLit q [139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151]) (count295 q) 2 (meaning282 q) (meaning296 q) hs
  change valuationOf q 282 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 282 = false ∨ valuation q 296 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 296 = false ∨ valuationOf q 298 = true := by
  have hs : count297 q = (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (296)) (literal (valuationOf q) (298)) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (count297 q) 2 (meaning296 q) (meaning298 q) hs
  change valuationOf q 296 = false ∨ valuationOf q 298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 296 = false ∨ valuation q 298 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]) + (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]) (l₂ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 298 = false ∨ valuationOf q 300 = true := by
  have hs : count299 q = (countLit q [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]) + (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]) (l₂ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (298)) (literal (valuationOf q) (300)) (countLit q [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (count299 q) 2 (meaning298 q) (meaning300 q) hs
  change valuationOf q 298 = false ∨ valuationOf q 300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 298 = false ∨ valuation q 300 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153, 154])
  have hm := merge_left (literal (valuationOf q) (152)) (literal (valuationOf q) (303)) (countLit q [152]) (countLit q [153, 154]) (count303 q) 1 (meaning152 q) (meaning303 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 303 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E154.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112154
