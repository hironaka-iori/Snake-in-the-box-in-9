import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 182 = true ∨ valuation q 5 = true ∨ valuation q 87 = true := by
  rw [value5, value60, value87, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(40 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (288 : Vertex) [(40 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 182 = true ∨ valuation q 5 = true ∨ valuation q 55 = true := by
  rw [value5, value55, value60, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(40 : Vertex), (288 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (424 : Vertex) [(40 : Vertex), (288 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 7 = false ∨ valuation q 63 = false ∨ valuation q 89 = false := by
  rw [value7, value61, value63, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (299 : Vertex) (43 : Vertex) (303 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 183 = true ∨ valuation q 63 = true ∨ valuation q 89 = true := by
  rw [value61, value63, value89, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (43 : Vertex) → w ∈ [(303 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (43 : Vertex) [(303 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 183 = true ∨ valuation q 7 = true ∨ valuation q 89 = true := by
  rw [value7, value61, value89, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(43 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (303 : Vertex) [(43 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 183 = true ∨ valuation q 7 = true ∨ valuation q 63 = true := by
  rw [value7, value61, value63, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(43 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (427 : Vertex) [(43 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 57 = false ∨ valuation q 63 = false ∨ valuation q 70 = false := by
  rw [value57, value62, value63, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (301 : Vertex) (293 : Vertex) (303 : Vertex) (317 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 184 = true ∨ valuation q 63 = true ∨ valuation q 70 = true := by
  rw [value62, value63, value70, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(303 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (293 : Vertex) [(303 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 184 = true ∨ valuation q 57 = true ∨ valuation q 70 = true := by
  rw [value57, value62, value70, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(293 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (303 : Vertex) [(293 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 184 = true ∨ valuation q 57 = true ∨ valuation q 63 = true := by
  rw [value57, value62, value63, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(293 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (317 : Vertex) [(293 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 59 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value59, value61, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 59 = false ∨ valuation q 61 = false ∨ valuation q 92 = false := by
  rw [value59, value61, value63, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (299 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 92 = false := by
  rw [value59, value62, value63, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (301 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 92 = false := by
  rw [value61, value62, value63, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (299 : Vertex) (301 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value61, value62, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (303 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 185 = true ∨ valuation q 59 = true ∨ valuation q 62 = true ∨ valuation q 92 = true := by
  rw [value59, value62, value63, value92, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (303 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(295 : Vertex), (301 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (303 : Vertex) (299 : Vertex) [(295 : Vertex), (301 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 185 = true ∨ valuation q 59 = true ∨ valuation q 61 = true ∨ valuation q 92 = true := by
  rw [value59, value61, value63, value92, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (303 : Vertex) w → w ∈ region → w ≠ (301 : Vertex) → w ∈ [(295 : Vertex), (299 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (303 : Vertex) (301 : Vertex) [(295 : Vertex), (299 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 186 = true ∨ valuation q 65 = true ∨ valuation q 66 = true := by
  rw [value64, value65, value66, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (304 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(305 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (304 : Vertex) (288 : Vertex) [(305 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 186 = true ∨ valuation q 55 = true ∨ valuation q 66 = true := by
  rw [value55, value64, value66, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (304 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(288 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (304 : Vertex) (305 : Vertex) [(288 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 186 = true ∨ valuation q 55 = true ∨ valuation q 65 = true := by
  rw [value55, value64, value65, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (304 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(288 : Vertex), (305 : Vertex)] := by decide
  have hg := other_cover q (304 : Vertex) (306 : Vertex) [(288 : Vertex), (305 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 56 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value56, value64, value65, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (289 : Vertex) (304 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 56 = false ∨ valuation q 64 = false ∨ valuation q 93 = false := by
  rw [value56, value64, value65, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (289 : Vertex) (304 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 56 = false ∨ valuation q 67 = false ∨ valuation q 93 = false := by
  rw [value56, value65, value67, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (289 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 93 = false := by
  rw [value64, value65, value67, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (304 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value64, value67, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (305 : Vertex) (304 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 187 = true ∨ valuation q 56 = true ∨ valuation q 64 = true ∨ valuation q 93 = true := by
  rw [value56, value64, value65, value93, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(289 : Vertex), (304 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (307 : Vertex) [(289 : Vertex), (304 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value64, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (304 : Vertex) (307 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value64, value67, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (306 : Vertex) (304 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 188 = true ∨ valuation q 64 = true ∨ valuation q 67 = true := by
  rw [value64, value66, value67, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (306 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(304 : Vertex), (307 : Vertex)] := by decide
  have hg := other_cover q (306 : Vertex) (310 : Vertex) [(304 : Vertex), (307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 94 = false := by
  rw [value65, value66, value67, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (305 : Vertex) (306 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 189 = true ∨ valuation q 66 = true ∨ valuation q 94 = true := by
  rw [value66, value67, value94, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(306 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(306 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 189 = true ∨ valuation q 65 = true ∨ valuation q 94 = true := by
  rw [value65, value67, value94, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(305 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (306 : Vertex) [(305 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.First112
