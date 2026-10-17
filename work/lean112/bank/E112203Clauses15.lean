import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 214 = true ∨ valuation q 95 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value95, value97, value99, value100, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(400 : Vertex), (406 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (403 : Vertex) [(400 : Vertex), (406 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 214 = true ∨ valuation q 95 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value95, value97, value98, value99, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(400 : Vertex), (403 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (410 : Vertex) [(400 : Vertex), (403 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 59 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value59, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (401 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 88 = false ∨ valuation q 97 = false ∨ valuation q 103 = false := by
  rw [value88, value97, value99, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (390 : Vertex) (402 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 29 = false ∨ valuation q 97 = false ∨ valuation q 103 = false := by
  rw [value29, value97, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (154 : Vertex) (402 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 65 = false ∨ valuation q 97 = false ∨ valuation q 103 = false := by
  rw [value65, value97, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (282 : Vertex) (402 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 218 = true ∨ valuation q 103 = true := by
  rw [value101, value103, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (413 : Vertex) [(414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 31 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value31, value93, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (157 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 219 = true ∨ valuation q 31 = true ∨ valuation q 93 = true := by
  rw [value31, value93, value102, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(157 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (412 : Vertex) [(157 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value99, value100, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 220 = true ∨ valuation q 100 = true ∨ valuation q 101 = true := by
  rw [value100, value101, value103, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(410 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (406 : Vertex) [(410 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 220 = true ∨ valuation q 99 = true ∨ valuation q 101 = true := by
  rw [value99, value101, value103, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(406 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (410 : Vertex) [(406 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 220 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value99, value100, value103, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(406 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (412 : Vertex) [(406 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = true := by
  rw [value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ∈ [(481 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (480 : Vertex) [(481 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 104 = true := by
  rw [value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 222 = true ∨ valuation q 110 = true := by
  rw [value105, value110, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (480 : Vertex) [(497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 223 = true ∨ valuation q 43 = true ∨ valuation q 113 = true := by
  rw [value43, value106, value113, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(230 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (487 : Vertex) [(230 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 223 = true ∨ valuation q 43 = true ∨ valuation q 107 = true := by
  rw [value43, value106, value107, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(230 : Vertex), (487 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (502 : Vertex) [(230 : Vertex), (487 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 224 = true ∨ valuation q 109 = true := by
  rw [value107, value109, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (486 : Vertex) [(495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 224 = true ∨ valuation q 106 = true := by
  rw [value106, value107, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(486 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (495 : Vertex) [(486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 225 = true ∨ valuation q 116 = true := by
  rw [value108, value116, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (495 : Vertex) [(509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 225 = true ∨ valuation q 109 = true := by
  rw [value108, value109, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(495 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (509 : Vertex) [(495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 226 = true ∨ valuation q 108 = true := by
  rw [value108, value109, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(493 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (487 : Vertex) [(493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 226 = true ∨ valuation q 107 = true := by
  rw [value107, value109, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(487 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (493 : Vertex) [(487 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 227 = true ∨ valuation q 112 = true := by
  rw [value110, value112, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(499 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (481 : Vertex) [(499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value111, value112, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (499 : Vertex) (502 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 228 = true ∨ valuation q 113 = true ∨ valuation q 114 = true := by
  rw [value111, value113, value114, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(502 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (499 : Vertex) [(502 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 229 = true ∨ valuation q 111 = true := by
  rw [value111, value112, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(498 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (497 : Vertex) [(498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 106 = false ∨ valuation q 111 = false ∨ valuation q 117 = false := by
  rw [value106, value111, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (486 : Vertex) (498 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 230 = true ∨ valuation q 106 = true ∨ valuation q 117 = true := by
  rw [value106, value113, value117, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(486 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (498 : Vertex) [(486 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 111 = true ∨ valuation q 117 = true := by
  rw [value111, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ∈ [(498 : Vertex), (510 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (506 : Vertex) [(498 : Vertex), (510 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 231 = true ∨ valuation q 117 = true := by
  rw [value114, value117, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(510 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (498 : Vertex) [(510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block15 (q : Snake 81) (h : Conditions q) : B112E203.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112203
