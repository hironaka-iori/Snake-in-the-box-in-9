import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 168 = true ∨ valuation q 38 = true ∨ valuation q 46 = true ∨ valuation q 48 = true := by
  rw [value38, value46, value47, value48, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(235 : Vertex), (250 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (249 : Vertex) [(235 : Vertex), (250 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 168 = true ∨ valuation q 38 = true ∨ valuation q 45 = true ∨ valuation q 46 = true := by
  rw [value38, value45, value46, value47, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(235 : Vertex), (249 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (255 : Vertex) [(235 : Vertex), (249 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 31 = false ∨ valuation q 43 = false ∨ valuation q 47 = false := by
  rw [value31, value43, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (191 : Vertex) (247 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 169 = true ∨ valuation q 31 = true ∨ valuation q 47 = true := by
  rw [value31, value47, value48, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(191 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (247 : Vertex) [(191 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 54 = false ∨ valuation q 58 = false := by
  rw [value49, value50, value54, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (304 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 58 = false ∨ valuation q 81 = false := by
  rw [value49, value50, value58, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (304 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 50 = false ∨ valuation q 58 = false := by
  rw [value50, value58, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (288 : Vertex) (289 : Vertex) (304 : Vertex) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 170 = true ∨ valuation q 54 = true ∨ valuation q 58 = true ∨ valuation q 81 = true := by
  rw [value49, value54, value58, value81, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(296 : Vertex), (304 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (289 : Vertex) [(296 : Vertex), (304 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 170 = true ∨ valuation q 50 = true ∨ valuation q 54 = true ∨ valuation q 81 = true := by
  rw [value49, value50, value54, value81, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (304 : Vertex) → w ∈ [(289 : Vertex), (296 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (304 : Vertex) [(289 : Vertex), (296 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 171 = true ∨ valuation q 51 = true ∨ valuation q 59 = true ∨ valuation q 82 = true := by
  rw [value50, value51, value59, value82, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(293 : Vertex), (305 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (288 : Vertex) [(293 : Vertex), (305 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 171 = true ∨ valuation q 49 = true ∨ valuation q 51 = true ∨ valuation q 82 = true := by
  rw [value49, value50, value51, value82, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(288 : Vertex), (293 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (305 : Vertex) [(288 : Vertex), (293 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 3 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value3, value51, value53, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (37 : Vertex) (295 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value50, value51, value53, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (289 : Vertex) (295 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 69 = false := by
  rw [value50, value51, value53, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (289 : Vertex) (295 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 85 = false := by
  rw [value50, value51, value53, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (289 : Vertex) (295 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 56 = false ∨ valuation q 69 = false := by
  rw [value50, value51, value56, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (289 : Vertex) (301 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 56 = false ∨ valuation q 85 = false := by
  rw [value50, value51, value56, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (289 : Vertex) (301 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 69 = false := by
  rw [value51, value53, value56, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (295 : Vertex) (301 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 85 = false := by
  rw [value51, value53, value56, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (295 : Vertex) (301 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 62 = false ∨ valuation q 86 = false := by
  rw [value52, value53, value62, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (295 : Vertex) (310 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 173 = true ∨ valuation q 53 = true ∨ valuation q 86 = true := by
  rw [value52, value53, value86, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(295 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (310 : Vertex) [(295 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 4 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value4, value51, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (39 : Vertex) (293 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 4 = false ∨ valuation q 52 = false ∨ valuation q 57 = false := by
  rw [value4, value52, value53, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (39 : Vertex) (294 : Vertex) (303 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 87 = false := by
  rw [value51, value52, value53, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (293 : Vertex) (294 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 174 = true ∨ valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 87 = true := by
  rw [value51, value52, value53, value57, value87, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (39 : Vertex) → w ∈ [(293 : Vertex), (294 : Vertex), (303 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (39 : Vertex) [(293 : Vertex), (294 : Vertex), (303 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 175 = true ∨ valuation q 88 = true := by
  rw [value54, value88, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (288 : Vertex) [(424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 175 = true ∨ valuation q 49 = true := by
  rw [value49, value54, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(288 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (424 : Vertex) [(288 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 71 = false ∨ valuation q 90 = false := by
  rw [value55, value57, value71, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (299 : Vertex) (303 : Vertex) (363 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 176 = true ∨ valuation q 71 = true ∨ valuation q 90 = true := by
  rw [value55, value71, value90, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(363 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (303 : Vertex) [(363 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 176 = true ∨ valuation q 57 = true ∨ valuation q 90 = true := by
  rw [value55, value57, value90, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(303 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (363 : Vertex) [(303 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 176 = true ∨ valuation q 57 = true ∨ valuation q 71 = true := by
  rw [value55, value57, value71, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(303 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (427 : Vertex) [(303 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 57 = false ∨ valuation q 64 = false := by
  rw [value51, value56, value57, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (301 : Vertex) (293 : Vertex) (303 : Vertex) (317 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E024.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112024
