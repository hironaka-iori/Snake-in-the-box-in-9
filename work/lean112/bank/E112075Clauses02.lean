import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 15 = false ∨ valuation q 62 = false ∨ valuation q 69 = false := by
  rw [value15, value61, value62, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (96 : Vertex) (353 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 15 = false ∨ valuation q 69 = false ∨ valuation q 90 = false := by
  rw [value15, value61, value69, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (96 : Vertex) (368 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 69 = false ∨ valuation q 90 = false := by
  rw [value61, value62, value69, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (353 : Vertex) (368 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 16 = false ∨ valuation q 66 = false ∨ valuation q 91 = false := by
  rw [value16, value62, value66, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (97 : Vertex) (361 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 67 = false := by
  rw [value62, value63, value65, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (353 : Vertex) (359 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 71 = false := by
  rw [value62, value63, value65, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (353 : Vertex) (359 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = false ∨ valuation q 67 = false ∨ valuation q 71 = false := by
  rw [value62, value63, value67, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (353 : Vertex) (363 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 71 = false := by
  rw [value63, value65, value67, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (359 : Vertex) (363 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 168 = true ∨ valuation q 62 = true ∨ valuation q 65 = true ∨ valuation q 71 = true := by
  rw [value62, value63, value65, value71, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(353 : Vertex), (359 : Vertex), (371 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (363 : Vertex) [(353 : Vertex), (359 : Vertex), (371 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 171 = true ∨ valuation q 62 = true := by
  rw [value62, value66, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(353 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (363 : Vertex) [(353 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 172 = true ∨ valuation q 66 = true ∨ valuation q 68 = true := by
  rw [value66, value67, value68, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (363 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(361 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (363 : Vertex) (355 : Vertex) [(361 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 172 = true ∨ valuation q 63 = true ∨ valuation q 68 = true := by
  rw [value63, value67, value68, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (363 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(355 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (363 : Vertex) (361 : Vertex) [(355 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 172 = true ∨ valuation q 63 = true ∨ valuation q 66 = true := by
  rw [value63, value66, value67, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (363 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(355 : Vertex), (361 : Vertex)] := by decide
  have hg := other_cover q (363 : Vertex) (367 : Vertex) [(355 : Vertex), (361 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 22 = false ∨ valuation q 65 = false ∨ valuation q 67 = false := by
  rw [value22, value65, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (359 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 22 = false ∨ valuation q 67 = false ∨ valuation q 97 = false := by
  rw [value22, value67, value68, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (363 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 97 = false := by
  rw [value65, value67, value68, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (359 : Vertex) (363 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 61 = true ∨ valuation q 70 = true := by
  rw [value61, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ∈ [(352 : Vertex), (370 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (368 : Vertex) [(352 : Vertex), (370 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 61 = false ∨ valuation q 70 = false := by
  rw [value61, value70, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (368 : Vertex) (352 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 69 = true := by
  rw [value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 174 = true := by
  rw [value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change BallClauseLogic.Endpoint q head
  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 175 = true ∨ valuation q 71 = true := by
  rw [value70, value71, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(371 : Vertex)] := by decide
  have hg := other_cover q (370 : Vertex) (368 : Vertex) [(371 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 176 = true ∨ valuation q 70 = true := by
  rw [value70, value71, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(370 : Vertex)] := by decide
  have hg := other_cover q (371 : Vertex) (355 : Vertex) [(370 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 176 = true ∨ valuation q 63 = true := by
  rw [value63, value71, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ≠ (370 : Vertex) → w ∈ [(355 : Vertex)] := by decide
  have hg := other_cover q (371 : Vertex) (370 : Vertex) [(355 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 82 = false ∨ valuation q 90 = false := by
  rw [value72, value73, value82, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (432 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 35 = false ∨ valuation q 74 = false ∨ valuation q 91 = false := by
  rw [value35, value73, value74, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (419 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 72 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value72, value73, value74, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (419 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value73, value74, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (419 : Vertex) (421 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 91 = false := by
  rw [value73, value74, value75, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (419 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 91 = false := by
  rw [value73, value74, value77, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (419 : Vertex) (425 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 91 = false := by
  rw [value73, value75, value77, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (421 : Vertex) (425 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 73 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value73, value74, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (417 : Vertex) (423 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 73 = false ∨ valuation q 76 = false ∨ valuation q 84 = false := by
  rw [value73, value74, value76, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (417 : Vertex) (423 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E075.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112075
