import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 93 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value93, value97, value98, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (389 : Vertex) (396 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 222 = true ∨ valuation q 97 = true ∨ valuation q 105 = true := by
  rw [value97, value98, value105, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(396 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (389 : Vertex) [(396 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 222 = true ∨ valuation q 93 = true ∨ valuation q 105 = true := by
  rw [value93, value98, value105, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(389 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (396 : Vertex) [(389 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 222 = true ∨ valuation q 93 = true ∨ valuation q 97 = true := by
  rw [value93, value97, value98, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(389 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (413 : Vertex) [(389 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 99 = true := by
  rw [value99, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (400 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 90 = true ∨ valuation q 100 = true ∨ valuation q 101 = true := by
  rw [value90, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ∈ [(384 : Vertex), (401 : Vertex), (402 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (400 : Vertex) [(384 : Vertex), (401 : Vertex), (402 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 223 = true ∨ valuation q 100 = true ∨ valuation q 101 = true := by
  rw [value99, value100, value101, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(401 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (400 : Vertex) (384 : Vertex) [(401 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 101 = true := by
  rw [value90, value99, value101, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(384 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (400 : Vertex) (401 : Vertex) [(384 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 100 = true := by
  rw [value90, value99, value100, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(384 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (400 : Vertex) (402 : Vertex) [(384 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 46 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value46, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (400 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 224 = true ∨ valuation q 46 = true ∨ valuation q 102 = true := by
  rw [value46, value100, value102, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(145 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (400 : Vertex) [(145 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 224 = true ∨ valuation q 46 = true ∨ valuation q 99 = true := by
  rw [value46, value99, value100, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(145 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (403 : Vertex) [(145 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 91 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value91, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (400 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 91 = false ∨ valuation q 99 = false ∨ valuation q 103 = false := by
  rw [value91, value99, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (400 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 91 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value91, value101, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (403 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value99, value101, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (403 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 225 = true ∨ valuation q 91 = true ∨ valuation q 102 = true ∨ valuation q 103 = true := by
  rw [value91, value101, value102, value103, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(386 : Vertex), (403 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (400 : Vertex) [(386 : Vertex), (403 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 225 = true ∨ valuation q 91 = true ∨ valuation q 99 = true ∨ valuation q 102 = true := by
  rw [value91, value99, value101, value102, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(386 : Vertex), (400 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (406 : Vertex) [(386 : Vertex), (400 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 92 = false ∨ valuation q 100 = false ∨ valuation q 116 = false := by
  rw [value92, value100, value102, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (387 : Vertex) (401 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 92 = false ∨ valuation q 101 = false ∨ valuation q 116 = false := by
  rw [value92, value101, value102, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (387 : Vertex) (402 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 226 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 116 = true := by
  rw [value100, value101, value102, value116, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(401 : Vertex), (402 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (387 : Vertex) [(401 : Vertex), (402 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 226 = true ∨ valuation q 92 = true ∨ valuation q 101 = true ∨ valuation q 116 = true := by
  rw [value92, value101, value102, value116, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(387 : Vertex), (402 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (401 : Vertex) [(387 : Vertex), (402 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 226 = true ∨ valuation q 92 = true ∨ valuation q 100 = true ∨ valuation q 116 = true := by
  rw [value92, value100, value102, value116, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(387 : Vertex), (401 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (402 : Vertex) [(387 : Vertex), (401 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 226 = true ∨ valuation q 92 = true ∨ valuation q 100 = true ∨ valuation q 101 = true := by
  rw [value92, value100, value101, value102, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(387 : Vertex), (401 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (467 : Vertex) [(387 : Vertex), (401 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 103 = true := by
  rw [value103, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (406 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 49 = true ∨ valuation q 101 = true ∨ valuation q 106 = true := by
  rw [value49, value101, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ∈ [(150 : Vertex), (402 : Vertex), (414 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (406 : Vertex) [(150 : Vertex), (402 : Vertex), (414 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 49 = false ∨ valuation q 101 = false ∨ valuation q 106 = false := by
  rw [value49, value101, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (150 : Vertex) (402 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 227 = true ∨ valuation q 101 = true ∨ valuation q 106 = true := by
  rw [value101, value103, value106, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(402 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (150 : Vertex) [(402 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 227 = true ∨ valuation q 49 = true ∨ valuation q 106 = true := by
  rw [value49, value103, value106, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(150 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (402 : Vertex) [(150 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 227 = true ∨ valuation q 49 = true ∨ valuation q 101 = true := by
  rw [value49, value101, value103, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(150 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (414 : Vertex) [(150 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 97 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value97, value104, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (412 : Vertex) (396 : Vertex) (413 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 228 = true ∨ valuation q 105 = true ∨ valuation q 106 = true := by
  rw [value104, value105, value106, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(413 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (396 : Vertex) [(413 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block26 (q : Snake 81) (h : Conditions q) : B112E089.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112089
