import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 224 = false := by
  rw [value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (411 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 227 = false := by
  rw [value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (449 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 228 = false := by
  rw [value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (450 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 233 = false := by
  rw [value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (459 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 235 = false := by
  rw [value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (461 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 236 = false := by
  rw [value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (462 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 238 = false := by
  rw [value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (464 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 242 = false := by
  rw [value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (469 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 243 = false := by
  rw [value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (470 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 244 = false := by
  rw [value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (474 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 245 = false := by
  rw [value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (476 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 248 = false := by
  rw [value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (479 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 126 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_left (literal (valuationOf q) (126)) (literal (valuationOf q) (249)) (countLit q [126]) (countLit q [127]) (count249 q) 1 (meaning126 q) (meaning249 q) hs
  change valuationOf q 126 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 249 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126, 127])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [125]) (countLit q [126, 127]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (253)) (countLit q [128]) (countLit q [129]) (count253 q) 1 (meaning128 q) (meaning253 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 253 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131])
  have hm := merge_right (literal (valuationOf q) (131)) (literal (valuationOf q) (255)) (countLit q [130]) (countLit q [131]) (count255 q) 1 (meaning131 q) (meaning255 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 255 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 130 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131])
  have hm := merge_left (literal (valuationOf q) (130)) (literal (valuationOf q) (255)) (countLit q [130]) (countLit q [131]) (count255 q) 1 (meaning130 q) (meaning255 q) hs
  change valuationOf q 130 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 255 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [128, 129]) (countLit q [130, 131]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (257)) (countLit q [128, 129]) (countLit q [130, 131]) (count257 q) 1 (meaning253 q) (meaning257 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 257 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (259)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count259 q) 1 (meaning251 q) (meaning259 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 259 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [132]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [134])
  have hm := merge_right (literal (valuationOf q) (134)) (literal (valuationOf q) (261)) (countLit q [132]) (countLit q [134]) (count261 q) 1 (meaning134 q) (meaning261 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 261 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [132, 134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [132, 134]) (l₂ := [135, 136])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (265)) (countLit q [132, 134]) (countLit q [135, 136]) (count265 q) 1 (meaning261 q) (meaning265 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 265 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 137 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_left (literal (valuationOf q) (137)) (literal (valuationOf q) (267)) (countLit q [137]) (countLit q [138]) (count267 q) 1 (meaning137 q) (meaning267 q) hs
  change valuationOf q 137 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 267 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_right (literal (valuationOf q) (140)) (literal (valuationOf q) (269)) (countLit q [139]) (countLit q [140]) (count269 q) 1 (meaning140 q) (meaning269 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 269 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [137, 138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [137, 138]) (l₂ := [139, 140])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [137, 138]) (countLit q [139, 140]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [137, 138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [137, 138]) (l₂ := [139, 140])
  have hm := merge_left (literal (valuationOf q) (267)) (literal (valuationOf q) (271)) (countLit q [137, 138]) (countLit q [139, 140]) (count271 q) 1 (meaning267 q) (meaning271 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 271 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [137, 138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [137, 138]) (l₂ := [139, 140])
  have hm := merge_two (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (literal (valuationOf q) (272)) (countLit q [137, 138]) (countLit q [139, 140]) (count271 q) 1 1 (meaning267 q) (meaning269 q) (meaning272 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = false ∨ valuation q 272 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [132, 134, 135, 136]) + (countLit q [137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [132, 134, 135, 136]) (l₂ := [137, 138, 139, 140])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [132, 134, 135, 136]) (countLit q [137, 138, 139, 140]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 272 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [132, 134, 135, 136]) + (countLit q [137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [132, 134, 135, 136]) (l₂ := [137, 138, 139, 140])
  have hm := merge_right (literal (valuationOf q) (272)) (literal (valuationOf q) (274)) (countLit q [132, 134, 135, 136]) (countLit q [137, 138, 139, 140]) (count273 q) 2 (meaning272 q) (meaning274 q) hs
  change valuationOf q 272 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 274 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [132, 134, 135, 136]) + (countLit q [137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [132, 134, 135, 136]) (l₂ := [137, 138, 139, 140])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (273)) (countLit q [132, 134, 135, 136]) (countLit q [137, 138, 139, 140]) (count273 q) 1 (meaning265 q) (meaning273 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 273 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [132, 134, 135, 136]) + (countLit q [137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [132, 134, 135, 136]) (l₂ := [137, 138, 139, 140])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (271)) (literal (valuationOf q) (274)) (countLit q [132, 134, 135, 136]) (countLit q [137, 138, 139, 140]) (count273 q) 1 1 (meaning265 q) (meaning271 q) (meaning274 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 271 = false ∨ valuation q 274 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E105.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112105
