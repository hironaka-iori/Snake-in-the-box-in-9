import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 79 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value79, value91, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (272 : Vertex) (320 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value91, value101, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (336 : Vertex) (320 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide)

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 227 = true ∨ valuation q 30 = true ∨ valuation q 79 = true ∨ valuation q 101 = true := by
  rw [value30, value79, value100, value101, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (336 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(80 : Vertex), (272 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (336 : Vertex) (320 : Vertex) [(80 : Vertex), (272 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 227 = true ∨ valuation q 30 = true ∨ valuation q 79 = true ∨ valuation q 91 = true := by
  rw [value30, value79, value91, value100, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (336 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(80 : Vertex), (272 : Vertex), (320 : Vertex)] := by decide
  have hg := other_cover q (336 : Vertex) (337 : Vertex) [(80 : Vertex), (272 : Vertex), (320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 92 = false ∨ valuation q 100 = false ∨ valuation q 104 = false := by
  rw [value92, value100, value101, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (337 : Vertex) (321 : Vertex) (336 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 228 = true ∨ valuation q 100 = true ∨ valuation q 104 = true := by
  rw [value100, value101, value104, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(336 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (321 : Vertex) [(336 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 228 = true ∨ valuation q 92 = true ∨ valuation q 104 = true := by
  rw [value92, value101, value104, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (336 : Vertex) → w ∈ [(321 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (336 : Vertex) [(321 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 228 = true ∨ valuation q 92 = true ∨ valuation q 100 = true := by
  rw [value92, value100, value101, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(321 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (345 : Vertex) [(321 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 102 = true := by
  rw [value102, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (342 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 83 = true ∨ valuation q 103 = true ∨ valuation q 107 = true := by
  rw [value83, value102, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ∈ [(278 : Vertex), (343 : Vertex), (350 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (342 : Vertex) [(278 : Vertex), (343 : Vertex), (350 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 83 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value83, value102, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (278 : Vertex) (343 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 83 = false ∨ valuation q 103 = false := by
  rw [value83, value103, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (342 : Vertex) (278 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide)

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 229 = true ∨ valuation q 83 = true ∨ valuation q 107 = true := by
  rw [value83, value102, value107, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(278 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (343 : Vertex) [(278 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 229 = true ∨ valuation q 83 = true ∨ valuation q 103 = true := by
  rw [value83, value102, value103, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(278 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (350 : Vertex) [(278 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 84 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value84, value102, value103, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (342 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 230 = true ∨ valuation q 102 = true ∨ valuation q 108 = true := by
  rw [value102, value103, value108, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(342 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (279 : Vertex) [(342 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 230 = true ∨ valuation q 84 = true ∨ valuation q 108 = true := by
  rw [value84, value103, value108, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(279 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (342 : Vertex) [(279 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 230 = true ∨ valuation q 84 = true ∨ valuation q 102 = true := by
  rw [value84, value102, value103, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (351 : Vertex) → w ∈ [(279 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (351 : Vertex) [(279 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 86 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value86, value101, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (281 : Vertex) (337 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value101, value105, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (345 : Vertex) (337 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide)

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 231 = true ∨ valuation q 86 = true ∨ valuation q 105 = true := by
  rw [value86, value104, value105, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(281 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (337 : Vertex) [(281 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 231 = true ∨ valuation q 86 = true ∨ valuation q 101 = true := by
  rw [value86, value101, value104, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(281 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (347 : Vertex) [(281 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 88 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value88, value104, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (283 : Vertex) (345 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 232 = true ∨ valuation q 104 = true ∨ valuation q 108 = true := by
  rw [value104, value105, value108, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(345 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (283 : Vertex) [(345 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 232 = true ∨ valuation q 88 = true ∨ valuation q 108 = true := by
  rw [value88, value105, value108, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(283 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (345 : Vertex) [(283 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 232 = true ∨ valuation q 88 = true ∨ valuation q 104 = true := by
  rw [value88, value104, value105, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (351 : Vertex) → w ∈ [(283 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (351 : Vertex) [(283 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 106 = true := by
  rw [value106, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (348 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 89 = false ∨ valuation q 97 = false := by
  rw [value36, value89, value97, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (92 : Vertex) (284 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 89 = false ∨ valuation q 107 = false := by
  rw [value36, value89, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (92 : Vertex) (284 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 89 = false ∨ valuation q 97 = false ∨ valuation q 107 = false := by
  rw [value89, value97, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (284 : Vertex) (332 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 233 = true ∨ valuation q 36 = true ∨ valuation q 89 = true ∨ valuation q 107 = true := by
  rw [value36, value89, value106, value107, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(92 : Vertex), (284 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (332 : Vertex) [(92 : Vertex), (284 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 99 = false ∨ valuation q 108 = false := by
  rw [value37, value99, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (334 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E057.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112057
