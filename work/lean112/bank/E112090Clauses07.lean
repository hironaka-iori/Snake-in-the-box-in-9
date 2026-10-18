import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 200 = true ∨ valuation q 86 = true ∨ valuation q 90 = true := by
  rw [value86, value90, value91, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(401 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (413 : Vertex) [(401 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 201 = true ∨ valuation q 90 = true := by
  rw [value90, value92, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(408 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (394 : Vertex) [(408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 201 = true ∨ valuation q 82 = true := by
  rw [value82, value92, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(394 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (408 : Vertex) [(394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value85, value87, value91, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (405 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 202 = true ∨ valuation q 85 = true ∨ valuation q 91 = true := by
  rw [value85, value91, value93, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(397 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (405 : Vertex) [(397 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 202 = true ∨ valuation q 85 = true ∨ valuation q 87 = true := by
  rw [value85, value87, value93, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(397 : Vertex), (405 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (409 : Vertex) [(397 : Vertex), (405 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value94, value95, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (483 : Vertex) (486 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 39 = false ∨ valuation q 94 = false ∨ valuation q 99 = false := by
  rw [value39, value94, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (482 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 204 = true ∨ valuation q 39 = true ∨ valuation q 94 = true := by
  rw [value39, value94, value95, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (483 : Vertex) w → w ∈ region → w ≠ (491 : Vertex) → w ∈ [(227 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (483 : Vertex) (491 : Vertex) [(227 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 205 = true ∨ valuation q 100 = true := by
  rw [value96, value100, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (484 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(492 : Vertex)] := by decide
  have hg := other_cover q (484 : Vertex) (486 : Vertex) [(492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 205 = true ∨ valuation q 97 = true := by
  rw [value96, value97, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (484 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(486 : Vertex)] := by decide
  have hg := other_cover q (484 : Vertex) (492 : Vertex) [(486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 104 = false := by
  rw [value94, value96, value97, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (484 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 94 = false ∨ valuation q 99 = false ∨ valuation q 108 = false := by
  rw [value94, value98, value99, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (482 : Vertex) (491 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 208 = true ∨ valuation q 98 = true := by
  rw [value98, value99, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(490 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (483 : Vertex) [(490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 208 = true ∨ valuation q 95 = true := by
  rw [value95, value99, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(483 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (490 : Vertex) [(483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 209 = true ∨ valuation q 101 = true := by
  rw [value100, value101, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (484 : Vertex) → w ∈ [(493 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (484 : Vertex) [(493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 210 = true ∨ valuation q 43 = true ∨ valuation q 109 = true := by
  rw [value43, value101, value109, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(237 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (492 : Vertex) [(237 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 213 = true ∨ valuation q 97 = true := by
  rw [value97, value104, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(486 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (503 : Vertex) [(486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 217 = true ∨ valuation q 98 = true := by
  rw [value98, value108, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(490 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (504 : Vertex) [(490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value101, value103, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (493 : Vertex) (501 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 112 = false := by
  rw [value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (107 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 113 = false := by
  rw [value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (117 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 117 = false := by
  rw [value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (121 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 118 = false := by
  rw [value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (122 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 123 = false := by
  rw [value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (133 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 125 = false := by
  rw [value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (137 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 127 = false := by
  rw [value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (140 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 129 = false := by
  rw [value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (143 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 132 = false := by
  rw [value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (146 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 133 = false := by
  rw [value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (148 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 136 = false := by
  rw [value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (158 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 138 = false := by
  rw [value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (194 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block7 (q : Snake 81) (h : Conditions q) : B112E090.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112090
