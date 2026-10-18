import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 28 = false ∨ valuation q 65 = false ∨ valuation q 81 = false := by
  rw [value28, value65, value81, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (136 : Vertex) (264 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 199 = true ∨ valuation q 28 = true ∨ valuation q 81 = true ∨ valuation q 86 = true := by
  rw [value28, value81, value85, value86, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(136 : Vertex), (384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (264 : Vertex) [(136 : Vertex), (384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 29 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value29, value82, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (385 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 29 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value29, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 29 = false ∨ valuation q 85 = false ∨ valuation q 101 = false := by
  rw [value29, value85, value86, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value82, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (385 : Vertex) (392 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 101 = false := by
  rw [value82, value85, value86, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (385 : Vertex) (392 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 101 = false := by
  rw [value85, value86, value87, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (392 : Vertex) (397 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 201 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 95 = true := by
  rw [value83, value86, value87, value95, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (399 : Vertex) [(389 : Vertex), (393 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 201 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 88 = true := by
  rw [value83, value86, value87, value88, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (413 : Vertex) [(389 : Vertex), (393 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value84, value87, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (399 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 202 = true ∨ valuation q 87 = true := by
  rw [value87, value88, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(397 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (391 : Vertex) [(397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 202 = true ∨ valuation q 84 = true := by
  rw [value84, value88, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(391 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (397 : Vertex) [(391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 203 = true ∨ valuation q 91 = true := by
  rw [value89, value91, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(403 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (385 : Vertex) [(403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value90, value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (403 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 204 = true ∨ valuation q 92 = true ∨ valuation q 93 = true := by
  rw [value90, value92, value93, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(406 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (403 : Vertex) [(406 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 205 = true ∨ valuation q 90 = true := by
  rw [value90, value91, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(402 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (401 : Vertex) [(402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 205 = true ∨ valuation q 89 = true := by
  rw [value89, value91, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(401 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (402 : Vertex) [(401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 90 = false ∨ valuation q 96 = false ∨ valuation q 109 = false := by
  rw [value90, value92, value96, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (402 : Vertex) (414 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 38 = false ∨ valuation q 90 = false ∨ valuation q 96 = false := by
  rw [value38, value90, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (154 : Vertex) (402 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 208 = true ∨ valuation q 96 = true := by
  rw [value94, value96, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (413 : Vertex) [(414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 208 = true ∨ valuation q 95 = true := by
  rw [value94, value95, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(413 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (414 : Vertex) [(413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 40 = false ∨ valuation q 87 = false ∨ valuation q 94 = false := by
  rw [value40, value87, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (157 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 209 = true ∨ valuation q 40 = true ∨ valuation q 94 = true := by
  rw [value40, value94, value95, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(157 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (397 : Vertex) [(157 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 209 = true ∨ valuation q 40 = true ∨ valuation q 87 = true := by
  rw [value40, value87, value95, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(157 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (412 : Vertex) [(157 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value92, value93, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 44 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value44, value97, value98, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (451 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value98, value102, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (450 : Vertex) (451 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 211 = true ∨ valuation q 44 = true ∨ valuation q 102 = true := by
  rw [value44, value97, value102, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(194 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (451 : Vertex) [(194 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 212 = true ∨ valuation q 97 = true ∨ valuation q 103 = true := by
  rw [value97, value98, value103, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (195 : Vertex) [(450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 212 = true ∨ valuation q 45 = true ∨ valuation q 103 = true := by
  rw [value45, value98, value103, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(195 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (450 : Vertex) [(195 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 212 = true ∨ valuation q 45 = true ∨ valuation q 97 = true := by
  rw [value45, value97, value98, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(195 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (459 : Vertex) [(195 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block12 (q : Snake 81) (h : Conditions q) : B112E168.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112168
