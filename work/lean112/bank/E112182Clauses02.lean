import E112182Semantics
import B112E182Inputs
namespace Snake9.Regrowth.E112182
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 176 = false := by
  rw [value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (391 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 183 = false := by
  rw [value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (403 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 192 = false := by
  rw [value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (487 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 193 = false := by
  rw [value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (488 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 202 = false := by
  rw [value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (508 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause70 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_left (literal (valuationOf q) (141)) (literal (valuationOf q) (275)) (countLit q [141]) (countLit q [142]) (count275 q) 1 (meaning141 q) (meaning275 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 275 = true := counterClause70 (baseVal q)

theorem counterClause71 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141, 142])
  have hm := merge_right (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (countLit q [140]) (countLit q [141, 142]) (count277 q) 1 (meaning275 q) (meaning277 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = true := counterClause71 (baseVal q)

theorem counterClause72 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [143]) + (countLit q [144, 145]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144, 145])
  have hm := merge_left (literal (valuationOf q) (143)) (literal (valuationOf q) (281)) (countLit q [143]) (countLit q [144, 145]) (count281 q) 1 (meaning143 q) (meaning281 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 281 = true := counterClause72 (baseVal q)

theorem counterClause73 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [140, 141, 142]) + (countLit q [143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142]) (l₂ := [143, 144, 145])
  have hm := merge_right (literal (valuationOf q) (281)) (literal (valuationOf q) (283)) (countLit q [140, 141, 142]) (countLit q [143, 144, 145]) (count283 q) 1 (meaning281 q) (meaning283 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = true := counterClause73 (baseVal q)

theorem counterClause74 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [140, 141, 142]) + (countLit q [143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142]) (l₂ := [143, 144, 145])
  have hm := merge_left (literal (valuationOf q) (277)) (literal (valuationOf q) (283)) (countLit q [140, 141, 142]) (countLit q [143, 144, 145]) (count283 q) 1 (meaning277 q) (meaning283 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 283 = true := counterClause74 (baseVal q)

theorem counterClause75 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 151, 152])
  have hm := merge_left (literal (valuationOf q) (283)) (literal (valuationOf q) (297)) (countLit q [140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 151, 152]) (count297 q) 1 (meaning283 q) (meaning297 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 297 = true := counterClause75 (baseVal q)

theorem counterClause76 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause76 (baseVal q)

theorem counterClause77 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]) + (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]) (l₂ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause77 (baseVal q)

theorem counterClause78 (q : Nat → Bool) : valuationOf q 153 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154, 155])
  have hm := merge_left (literal (valuationOf q) (153)) (literal (valuationOf q) (305)) (countLit q [153]) (countLit q [154, 155]) (count305 q) 1 (meaning153 q) (meaning305 q) hs
  change valuationOf q 153 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 305 = true := counterClause78 (baseVal q)

theorem counterClause79 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_left (literal (valuationOf q) (157)) (literal (valuationOf q) (307)) (countLit q [157]) (countLit q [158]) (count307 q) 1 (meaning157 q) (meaning307 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 307 = true := counterClause79 (baseVal q)

theorem counterClause80 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157, 158])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [156]) (countLit q [157, 158]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause80 (baseVal q)

theorem counterClause81 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [153, 154, 155]) + (countLit q [156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155]) (l₂ := [156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [153, 154, 155]) (countLit q [156, 157, 158]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause81 (baseVal q)

theorem counterClause82 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [153, 154, 155]) + (countLit q [156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155]) (l₂ := [156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (311)) (countLit q [153, 154, 155]) (countLit q [156, 157, 158]) (count311 q) 1 (meaning305 q) (meaning311 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 311 = true := counterClause82 (baseVal q)

theorem counterClause83 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [153, 154, 155]) + (countLit q [156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155]) (l₂ := [156, 157, 158])
  have hm := merge_two (literal (valuationOf q) (305)) (literal (valuationOf q) (309)) (literal (valuationOf q) (312)) (countLit q [153, 154, 155]) (countLit q [156, 157, 158]) (count311 q) 1 1 (meaning305 q) (meaning309 q) (meaning312 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 309 = false ∨ valuation q 312 = true := counterClause83 (baseVal q)

theorem counterClause84 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (323)) (countLit q [153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164]) (count323 q) 1 (meaning311 q) (meaning323 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 323 = true := counterClause84 (baseVal q)

theorem counterClause85 (q : Nat → Bool) : valuationOf q 312 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164])
  have hm := merge_left (literal (valuationOf q) (312)) (literal (valuationOf q) (324)) (countLit q [153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164]) (count323 q) 2 (meaning312 q) (meaning324 q) hs
  change valuationOf q 312 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 312 = false ∨ valuation q 324 = true := counterClause85 (baseVal q)

theorem counterClause86 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (349)) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178]) (count349 q) 1 (meaning323 q) (meaning349 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 349 = true := counterClause86 (baseVal q)

theorem counterClause87 (q : Nat → Bool) : valuationOf q 324 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (324)) (literal (valuationOf q) (350)) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178]) (count349 q) 2 (meaning324 q) (meaning350 q) hs
  change valuationOf q 324 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 324 = false ∨ valuation q 350 = true := counterClause87 (baseVal q)

theorem counterClause88 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (349)) (literal (valuationOf q) (401)) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count401 q) 1 (meaning349 q) (meaning401 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 401 = true := counterClause88 (baseVal q)

theorem counterClause89 (q : Nat → Bool) : valuationOf q 350 = false ∨ valuationOf q 402 = true := by
  have hs : count401 q = (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (350)) (literal (valuationOf q) (402)) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count401 q) 2 (meaning350 q) (meaning402 q) hs
  change valuationOf q 350 = false ∨ valuationOf q 402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 350 = false ∨ valuation q 402 = true := counterClause89 (baseVal q)

theorem counterClause90 (q : Nat → Bool) : valuationOf q 402 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_right (literal (valuationOf q) (402)) (literal (valuationOf q) (404)) (countLit q [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count403 q) 2 (meaning402 q) (meaning404 q) hs
  change valuationOf q 402 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 402 = false ∨ valuation q 404 = true := counterClause90 (baseVal q)

theorem counterClause91 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_two (literal (valuationOf q) (301)) (literal (valuationOf q) (401)) (literal (valuationOf q) (404)) (countLit q [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count403 q) 1 1 (meaning301 q) (meaning401 q) (meaning404 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 401 = false ∨ valuation q 404 = true := counterClause91 (baseVal q)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 404 = false := by
  rw [value404]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count403 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause93 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1221 = true := by
  have hs : count1221 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1221)) (countLit q [-6]) (countLit q [-7]) (count1221 q) 1 (meaningNeg7 q) (meaning1221 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1221 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1221 = true := counterClause93 (baseVal q)

theorem counterClause94 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1221 = true := by
  have hs : count1221 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1221)) (countLit q [-6]) (countLit q [-7]) (count1221 q) 1 (meaningNeg6 q) (meaning1221 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1221 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1221 = true := counterClause94 (baseVal q)

theorem counterClause95 (q : Nat → Bool) : valuationOf q 1221 = false ∨ valuationOf q 1223 = true := by
  have hs : count1223 q = (countLit q [-5]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (1221)) (literal (valuationOf q) (1223)) (countLit q [-5]) (countLit q [-6, -7]) (count1223 q) 1 (meaning1221 q) (meaning1223 q) hs
  change valuationOf q 1221 = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 1221 = false ∨ valuation q 1223 = true := counterClause95 (baseVal q)

theorem counterClause96 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1223 = true := by
  have hs : count1223 q = (countLit q [-5]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-6, -7])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (1223)) (countLit q [-5]) (countLit q [-6, -7]) (count1223 q) 1 (meaningNeg5 q) (meaning1223 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1223 = true := counterClause96 (baseVal q)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E182.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112182
