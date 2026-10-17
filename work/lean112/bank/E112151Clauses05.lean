import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 29 = false ∨ valuation q 63 = false ∨ valuation q 93 = false := by
  rw [value29, value63, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (201 : Vertex) (329 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 29 = false ∨ valuation q 63 = false ∨ valuation q 101 = false := by
  rw [value29, value63, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (201 : Vertex) (329 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 29 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value29, value93, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (201 : Vertex) (456 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 63 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value63, value93, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (329 : Vertex) (456 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 202 = true ∨ valuation q 97 = true := by
  rw [value95, value97, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(474 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (456 : Vertex) [(474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 202 = true ∨ valuation q 93 = true := by
  rw [value93, value95, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(456 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (474 : Vertex) [(456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 203 = true := by
  rw [value96, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (473 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (473 : Vertex) (457 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 37 = false ∨ valuation q 71 = false ∨ valuation q 95 = false := by
  rw [value37, value71, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 37 = false ∨ valuation q 95 = false ∨ valuation q 106 = false := by
  rw [value37, value95, value97, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (458 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 204 = true ∨ valuation q 71 = true ∨ valuation q 95 = true ∨ valuation q 106 = true := by
  rw [value71, value95, value97, value106, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (474 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(346 : Vertex), (458 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (474 : Vertex) (218 : Vertex) [(346 : Vertex), (458 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 205 = true := by
  rw [value98, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (480 : Vertex) (482 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 206 = true ∨ valuation q 98 = true ∨ valuation q 105 = true := by
  rw [value98, value99, value105, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(480 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (486 : Vertex) [(480 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 206 = true ∨ valuation q 98 = true ∨ valuation q 100 = true := by
  rw [value98, value99, value100, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(480 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (498 : Vertex) [(480 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 99 = false ∨ valuation q 104 = false := by
  rw [value78, value99, value100, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (422 : Vertex) (482 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 207 = true ∨ valuation q 78 = true ∨ valuation q 99 = true := by
  rw [value78, value99, value100, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (494 : Vertex) → w ∈ [(422 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (494 : Vertex) [(422 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 208 = true ∨ valuation q 81 = true ∨ valuation q 94 = true := by
  rw [value81, value94, value101, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (489 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(425 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (489 : Vertex) (493 : Vertex) [(425 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 209 = true ∨ valuation q 104 = true ∨ valuation q 107 = true := by
  rw [value102, value104, value107, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(494 : Vertex), (508 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (493 : Vertex) [(494 : Vertex), (508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 209 = true ∨ valuation q 103 = true ∨ valuation q 104 = true := by
  rw [value102, value103, value104, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (508 : Vertex) → w ∈ [(493 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (508 : Vertex) [(493 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 210 = true ∨ valuation q 101 = true := by
  rw [value101, value103, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(489 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (492 : Vertex) [(489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 211 = true ∨ valuation q 100 = true := by
  rw [value100, value104, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (494 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(486 : Vertex)] := by decide
  have hg := other_cover q (494 : Vertex) (492 : Vertex) [(486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 85 = false ∨ valuation q 99 = false ∨ valuation q 106 = false := by
  rw [value85, value99, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (434 : Vertex) (482 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 212 = true ∨ valuation q 99 = true ∨ valuation q 106 = true := by
  rw [value99, value105, value106, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(482 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (434 : Vertex) [(482 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 212 = true ∨ valuation q 85 = true ∨ valuation q 106 = true := by
  rw [value85, value105, value106, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(434 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (482 : Vertex) [(434 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 212 = true ∨ valuation q 85 = true ∨ valuation q 99 = true := by
  rw [value85, value99, value105, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(434 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (506 : Vertex) [(434 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 90 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value90, value97, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (506 : Vertex) (442 : Vertex) (474 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 108 = false := by
  rw [value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (0 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 110 = false := by
  rw [value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (18 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 112 = false := by
  rw [value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (58 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 116 = false := by
  rw [value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (123 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 117 = false := by
  rw [value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (160 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 121 = false := by
  rw [value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (172 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 127 = false := by
  rw [value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (183 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block5 (q : Snake 81) (h : Conditions q) : B112E151.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112151
