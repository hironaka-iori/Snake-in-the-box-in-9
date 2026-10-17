import E112179Semantics
import B112E179Inputs
namespace Snake9.Regrowth.E112179
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 20 = false ∨ valuation q 35 = false ∨ valuation q 37 = false := by
  rw [value20, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 32 = false ∨ valuation q 35 = false ∨ valuation q 37 = false := by
  rw [value32, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 143 = true ∨ valuation q 41 = true := by
  rw [value39, value41, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(211 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (193 : Vertex) [(211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value40, value41, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (211 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 33 = true ∨ valuation q 40 = true ∨ valuation q 46 = true := by
  rw [value33, value40, value42, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ∈ [(198 : Vertex), (210 : Vertex), (222 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (214 : Vertex) [(198 : Vertex), (210 : Vertex), (222 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 147 = true ∨ valuation q 40 = true ∨ valuation q 46 = true := by
  rw [value40, value43, value46, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(210 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (154 : Vertex) [(210 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 148 = true ∨ valuation q 46 = true := by
  rw [value44, value46, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (221 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value42, value43, value44, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 151 = true ∨ valuation q 49 = true := by
  rw [value47, value49, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(296 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (289 : Vertex) [(296 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 152 = true ∨ valuation q 47 = true := by
  rw [value47, value48, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(288 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (305 : Vertex) [(288 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 49 = true := by
  rw [value49, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (296 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 153 = true ∨ valuation q 86 = true := by
  rw [value49, value86, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (288 : Vertex) [(424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 154 = true ∨ valuation q 48 = true := by
  rw [value48, value50, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(289 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (307 : Vertex) [(289 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 155 = true ∨ valuation q 52 = true := by
  rw [value51, value52, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (306 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(307 : Vertex)] := by decide
  have hg := other_cover q (306 : Vertex) (310 : Vertex) [(307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 156 = true ∨ valuation q 50 = true := by
  rw [value50, value52, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(305 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (306 : Vertex) [(305 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 157 = true ∨ valuation q 51 = true := by
  rw [value51, value53, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(306 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (318 : Vertex) [(306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 158 = true ∨ valuation q 56 = true := by
  rw [value54, value56, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(318 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (317 : Vertex) [(318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 54 = true := by
  rw [value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ∈ [(316 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (317 : Vertex) [(316 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 55 = true := by
  rw [value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 160 = true ∨ valuation q 53 = true := by
  rw [value53, value56, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (318 : Vertex) w → w ∈ region → w ≠ (316 : Vertex) → w ∈ [(310 : Vertex)] := by decide
  have hg := other_cover q (318 : Vertex) (316 : Vertex) [(310 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 8 = false ∨ valuation q 58 = false ∨ valuation q 61 = false := by
  rw [value8, value57, value58, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (64 : Vertex) (321 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 161 = true ∨ valuation q 8 = true ∨ valuation q 61 = true := by
  rw [value8, value57, value61, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(64 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (321 : Vertex) [(64 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 161 = true ∨ valuation q 8 = true ∨ valuation q 58 = true := by
  rw [value8, value57, value58, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(64 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (328 : Vertex) [(64 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 162 = true ∨ valuation q 62 = true ∨ valuation q 65 = true := by
  rw [value58, value62, value65, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(329 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(329 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 162 = true ∨ valuation q 57 = true ∨ valuation q 62 = true := by
  rw [value57, value58, value62, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(320 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (337 : Vertex) [(320 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 10 = false ∨ valuation q 60 = false ∨ valuation q 69 = false := by
  rw [value10, value59, value60, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (70 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 163 = true ∨ valuation q 10 = true ∨ valuation q 69 = true := by
  rw [value10, value59, value69, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(70 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (327 : Vertex) [(70 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 59 = true ∨ valuation q 64 = true := by
  rw [value59, value60, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ∈ [(326 : Vertex), (335 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (327 : Vertex) [(326 : Vertex), (335 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 164 = true ∨ valuation q 64 = true := by
  rw [value60, value64, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(335 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 164 = true ∨ valuation q 59 = true := by
  rw [value59, value60, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(326 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (335 : Vertex) [(326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 61 = true := by
  rw [value61, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (328 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 11 = true ∨ valuation q 57 = true ∨ valuation q 62 = true := by
  rw [value11, value57, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ∈ [(72 : Vertex), (320 : Vertex), (329 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (328 : Vertex) [(72 : Vertex), (320 : Vertex), (329 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E179.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112179
