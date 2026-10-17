import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 224 = false := by
  rw [value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (362 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 226 = false := by
  rw [value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (367 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 228 = false := by
  rw [value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (375 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 229 = false := by
  rw [value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (448 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 231 = false := by
  rw [value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (451 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 233 = false := by
  rw [value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (453 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 234 = false := by
  rw [value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (454 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 236 = false := by
  rw [value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (457 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 239 = false := by
  rw [value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (466 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 241 = false := by
  rw [value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (468 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 243 = false := by
  rw [value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (482 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 245 = false := by
  rw [value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (484 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 247 = false := by
  rw [value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (487 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 248 = false := by
  rw [value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (488 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 250 = false := by
  rw [value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (491 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 252 = false := by
  rw [value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (493 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause881 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_left (literal (valuationOf q) (129)) (literal (valuationOf q) (255)) (countLit q [129]) (countLit q [130]) (count255 q) 1 (meaning129 q) (meaning255 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 255 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129, 130])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [128]) (countLit q [129, 130]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129, 130])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (257)) (countLit q [128]) (countLit q [129, 130]) (count257 q) 1 (meaning128 q) (meaning257 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 257 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129, 130])
  have hm := merge_two (literal (valuationOf q) (128)) (literal (valuationOf q) (255)) (literal (valuationOf q) (258)) (countLit q [128]) (countLit q [129, 130]) (count257 q) 1 1 (meaning128 q) (meaning255 q) (meaning258 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 255 = false ∨ valuation q 258 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_right (literal (valuationOf q) (132)) (literal (valuationOf q) (259)) (countLit q [131]) (countLit q [132]) (count259 q) 1 (meaning132 q) (meaning259 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 259 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_right (literal (valuationOf q) (134)) (literal (valuationOf q) (261)) (countLit q [133]) (countLit q [134]) (count261 q) 1 (meaning134 q) (meaning261 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 261 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (261)) (countLit q [133]) (countLit q [134]) (count261 q) 1 (meaning133 q) (meaning261 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 261 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 134 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_two (literal (valuationOf q) (133)) (literal (valuationOf q) (134)) (literal (valuationOf q) (262)) (countLit q [133]) (countLit q [134]) (count261 q) 1 1 (meaning133 q) (meaning134 q) (meaning262 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 134 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 134 = false ∨ valuation q 262 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [131, 132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [131, 132]) (l₂ := [133, 134])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [131, 132]) (countLit q [133, 134]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 262 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [131, 132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [131, 132]) (l₂ := [133, 134])
  have hm := merge_right (literal (valuationOf q) (262)) (literal (valuationOf q) (264)) (countLit q [131, 132]) (countLit q [133, 134]) (count263 q) 2 (meaning262 q) (meaning264 q) hs
  change valuationOf q 262 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 262 = false ∨ valuation q 264 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [131, 132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [131, 132]) (l₂ := [133, 134])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (263)) (countLit q [131, 132]) (countLit q [133, 134]) (count263 q) 1 (meaning259 q) (meaning263 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 263 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 264 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (264)) (literal (valuationOf q) (266)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count265 q) 2 (meaning264 q) (meaning266 q) hs
  change valuationOf q 264 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 264 = false ∨ valuation q 266 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (265)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count265 q) 1 (meaning257 q) (meaning265 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 265 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_two (literal (valuationOf q) (257)) (literal (valuationOf q) (263)) (literal (valuationOf q) (266)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count265 q) 1 1 (meaning257 q) (meaning263 q) (meaning266 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 263 = false ∨ valuation q 266 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 258 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (258)) (literal (valuationOf q) (266)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count265 q) 2 (meaning258 q) (meaning266 q) hs
  change valuationOf q 258 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 258 = false ∨ valuation q 266 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E260.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112260
