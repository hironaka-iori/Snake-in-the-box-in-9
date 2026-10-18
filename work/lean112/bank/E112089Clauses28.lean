import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 107 = false ∨ valuation q 113 = false ∨ valuation q 120 = false := by
  rw [value107, value112, value113, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (448 : Vertex) (457 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 107 = true ∨ valuation q 113 = true ∨ valuation q 120 = true := by
  rw [value107, value112, value113, value120, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (456 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(448 : Vertex), (457 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (456 : Vertex) (200 : Vertex) [(448 : Vertex), (457 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 62 = true ∨ valuation q 113 = true ∨ valuation q 120 = true := by
  rw [value62, value112, value113, value120, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (456 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(200 : Vertex), (457 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (456 : Vertex) (448 : Vertex) [(200 : Vertex), (457 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 62 = true ∨ valuation q 107 = true ∨ valuation q 120 = true := by
  rw [value62, value107, value112, value120, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (456 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(200 : Vertex), (448 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (456 : Vertex) (457 : Vertex) [(200 : Vertex), (448 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 62 = true ∨ valuation q 107 = true ∨ valuation q 113 = true := by
  rw [value62, value107, value112, value113, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (456 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(200 : Vertex), (448 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (456 : Vertex) (472 : Vertex) [(200 : Vertex), (448 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 113 = true := by
  rw [value113, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (457 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 63 = true ∨ valuation q 108 = true ∨ valuation q 112 = true := by
  rw [value63, value108, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ∈ [(201 : Vertex), (449 : Vertex), (456 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (457 : Vertex) [(201 : Vertex), (449 : Vertex), (456 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 108 = true ∨ valuation q 112 = true := by
  rw [value108, value112, value113, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(449 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (201 : Vertex) [(449 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 63 = true ∨ valuation q 112 = true := by
  rw [value63, value112, value113, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(201 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (449 : Vertex) [(201 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 63 = true ∨ valuation q 108 = true := by
  rw [value63, value108, value113, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(201 : Vertex), (449 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (456 : Vertex) [(201 : Vertex), (449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 67 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value67, value111, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (454 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 238 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value111, value114, value115, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(454 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (206 : Vertex) [(454 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 238 = true ∨ valuation q 67 = true ∨ valuation q 115 = true := by
  rw [value67, value114, value115, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (454 : Vertex) → w ∈ [(206 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (454 : Vertex) [(206 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 238 = true ∨ valuation q 67 = true ∨ valuation q 111 = true := by
  rw [value67, value111, value114, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(206 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (463 : Vertex) [(206 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 115 = true := by
  rw [value115, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (463 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 68 = true ∨ valuation q 114 = true ∨ valuation q 124 = true := by
  rw [value68, value114, value115, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ∈ [(207 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (463 : Vertex) [(207 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 68 = false ∨ valuation q 114 = false ∨ valuation q 124 = false := by
  rw [value68, value114, value115, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (207 : Vertex) (462 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 68 = false ∨ valuation q 114 = false := by
  rw [value68, value114, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (463 : Vertex) (207 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide)

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 239 = true ∨ valuation q 114 = true ∨ valuation q 124 = true := by
  rw [value114, value115, value124, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (207 : Vertex) [(462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 239 = true ∨ valuation q 68 = true ∨ valuation q 124 = true := by
  rw [value68, value115, value124, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(207 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (462 : Vertex) [(207 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 239 = true ∨ valuation q 68 = true ∨ valuation q 114 = true := by
  rw [value68, value114, value115, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(207 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (479 : Vertex) [(207 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 72 = false ∨ valuation q 102 = false ∨ valuation q 119 = false := by
  rw [value72, value102, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (211 : Vertex) (403 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 72 = false ∨ valuation q 102 = false ∨ valuation q 122 = false := by
  rw [value72, value102, value116, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (211 : Vertex) (403 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 72 = false ∨ valuation q 119 = false ∨ valuation q 122 = false := by
  rw [value72, value116, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (211 : Vertex) (471 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 102 = false ∨ valuation q 119 = false ∨ valuation q 122 = false := by
  rw [value102, value116, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (403 : Vertex) (471 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 240 = true ∨ valuation q 72 = true ∨ valuation q 119 = true ∨ valuation q 122 = true := by
  rw [value72, value116, value119, value122, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(211 : Vertex), (471 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (403 : Vertex) [(211 : Vertex), (471 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 240 = true ∨ valuation q 72 = true ∨ valuation q 102 = true ∨ valuation q 119 = true := by
  rw [value72, value102, value116, value119, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(211 : Vertex), (403 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (475 : Vertex) [(211 : Vertex), (403 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 117 = true := by
  rw [value117, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (468 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 110 = true ∨ valuation q 118 = true := by
  rw [value110, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ∈ [(452 : Vertex), (469 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (468 : Vertex) [(452 : Vertex), (469 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 241 = true ∨ valuation q 118 = true := by
  rw [value117, value118, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(469 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (452 : Vertex) [(469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 241 = true ∨ valuation q 110 = true := by
  rw [value110, value117, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(452 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (469 : Vertex) [(452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 117 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value117, value118, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (468 : Vertex) (471 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E089.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112089
