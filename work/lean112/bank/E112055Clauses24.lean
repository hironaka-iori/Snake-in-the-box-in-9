import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 227 = true ∨ valuation q 96 = true ∨ valuation q 107 = true := by
  rw [value96, value99, value107, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(330 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (332 : Vertex) [(330 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 227 = true ∨ valuation q 96 = true ∨ valuation q 97 = true := by
  rw [value96, value97, value99, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(330 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (350 : Vertex) [(330 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 30 = false ∨ valuation q 92 = false ∨ valuation q 101 = false := by
  rw [value30, value92, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (320 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 80 = false ∨ valuation q 92 = false ∨ valuation q 101 = false := by
  rw [value80, value92, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (272 : Vertex) (320 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 228 = true ∨ valuation q 30 = true ∨ valuation q 80 = true ∨ valuation q 101 = true := by
  rw [value30, value80, value100, value101, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (336 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(80 : Vertex), (272 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (336 : Vertex) (320 : Vertex) [(80 : Vertex), (272 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 228 = true ∨ valuation q 30 = true ∨ valuation q 80 = true ∨ valuation q 92 = true := by
  rw [value30, value80, value92, value100, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (336 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(80 : Vertex), (272 : Vertex), (320 : Vertex)] := by decide
  have hg := other_cover q (336 : Vertex) (337 : Vertex) [(80 : Vertex), (272 : Vertex), (320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 93 = false ∨ valuation q 100 = false ∨ valuation q 104 = false := by
  rw [value93, value100, value101, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (337 : Vertex) (321 : Vertex) (336 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 229 = true ∨ valuation q 100 = true ∨ valuation q 104 = true := by
  rw [value100, value101, value104, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(336 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (321 : Vertex) [(336 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 229 = true ∨ valuation q 93 = true ∨ valuation q 104 = true := by
  rw [value93, value101, value104, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (336 : Vertex) → w ∈ [(321 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (336 : Vertex) [(321 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 229 = true ∨ valuation q 93 = true ∨ valuation q 100 = true := by
  rw [value93, value100, value101, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(321 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (345 : Vertex) [(321 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 102 = true := by
  rw [value102, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (342 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 84 = true ∨ valuation q 103 = true ∨ valuation q 107 = true := by
  rw [value84, value102, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ∈ [(278 : Vertex), (343 : Vertex), (350 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (342 : Vertex) [(278 : Vertex), (343 : Vertex), (350 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 84 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value84, value102, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (278 : Vertex) (343 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 84 = false ∨ valuation q 107 = false := by
  rw [value84, value107, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (342 : Vertex) (278 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide)

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 230 = true ∨ valuation q 103 = true ∨ valuation q 107 = true := by
  rw [value102, value103, value107, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(343 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (278 : Vertex) [(343 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 230 = true ∨ valuation q 84 = true ∨ valuation q 107 = true := by
  rw [value84, value102, value107, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(278 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (343 : Vertex) [(278 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 230 = true ∨ valuation q 84 = true ∨ valuation q 103 = true := by
  rw [value84, value102, value103, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(278 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (350 : Vertex) [(278 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 85 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value85, value102, value103, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (342 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 231 = true ∨ valuation q 102 = true ∨ valuation q 108 = true := by
  rw [value102, value103, value108, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(342 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (279 : Vertex) [(342 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 231 = true ∨ valuation q 85 = true ∨ valuation q 108 = true := by
  rw [value85, value103, value108, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(279 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (342 : Vertex) [(279 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 231 = true ∨ valuation q 85 = true ∨ valuation q 102 = true := by
  rw [value85, value102, value103, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (351 : Vertex) → w ∈ [(279 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (351 : Vertex) [(279 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 104 = true := by
  rw [value104, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (345 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 87 = true ∨ valuation q 101 = true ∨ valuation q 105 = true := by
  rw [value87, value101, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ∈ [(281 : Vertex), (337 : Vertex), (347 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (345 : Vertex) [(281 : Vertex), (337 : Vertex), (347 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 87 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value87, value101, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (281 : Vertex) (337 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 87 = false ∨ valuation q 101 = false := by
  rw [value87, value101, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (345 : Vertex) (281 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide)

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 232 = true ∨ valuation q 101 = true ∨ valuation q 105 = true := by
  rw [value101, value104, value105, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(337 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (281 : Vertex) [(337 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 232 = true ∨ valuation q 87 = true ∨ valuation q 105 = true := by
  rw [value87, value104, value105, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(281 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (337 : Vertex) [(281 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 232 = true ∨ valuation q 87 = true ∨ valuation q 101 = true := by
  rw [value87, value101, value104, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(281 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (347 : Vertex) [(281 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 89 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value89, value104, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (283 : Vertex) (345 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 233 = true ∨ valuation q 104 = true ∨ valuation q 108 = true := by
  rw [value104, value105, value108, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(345 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (283 : Vertex) [(345 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 233 = true ∨ valuation q 89 = true ∨ valuation q 108 = true := by
  rw [value89, value105, value108, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(283 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (345 : Vertex) [(283 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 233 = true ∨ valuation q 89 = true ∨ valuation q 104 = true := by
  rw [value89, value104, value105, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (351 : Vertex) → w ∈ [(283 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (351 : Vertex) [(283 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block24 (q : Snake 81) (h : Conditions q) : B112E055.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112055
