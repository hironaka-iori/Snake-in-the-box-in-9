import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 170 = true ∨ valuation q 50 = true ∨ valuation q 57 = true ∨ valuation q 81 = true := by
  rw [value49, value50, value57, value81, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(289 : Vertex), (304 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (296 : Vertex) [(289 : Vertex), (304 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 170 = true ∨ valuation q 50 = true ∨ valuation q 53 = true ∨ valuation q 81 = true := by
  rw [value49, value50, value53, value81, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (304 : Vertex) → w ∈ [(289 : Vertex), (296 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (304 : Vertex) [(289 : Vertex), (296 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 49 = false ∨ valuation q 58 = false ∨ valuation q 82 = false := by
  rw [value49, value50, value58, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (288 : Vertex) (305 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 171 = true ∨ valuation q 58 = true ∨ valuation q 82 = true := by
  rw [value50, value58, value82, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(305 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (288 : Vertex) [(305 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 171 = true ∨ valuation q 49 = true ∨ valuation q 82 = true := by
  rw [value49, value50, value82, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(288 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (305 : Vertex) [(288 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 171 = true ∨ valuation q 49 = true ∨ valuation q 58 = true := by
  rw [value49, value50, value58, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(288 : Vertex), (305 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (417 : Vertex) [(288 : Vertex), (305 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 62 = false ∨ valuation q 86 = false := by
  rw [value51, value52, value62, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (295 : Vertex) (310 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 62 = false ∨ valuation q 86 = false := by
  rw [value62, value86, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (294 : Vertex) (310 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 172 = true ∨ valuation q 52 = true ∨ valuation q 86 = true := by
  rw [value51, value52, value86, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(295 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (310 : Vertex) [(295 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 51 = false ∨ valuation q 56 = false := by
  rw [value4, value51, value52, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (39 : Vertex) (294 : Vertex) (303 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 56 = false ∨ valuation q 87 = false := by
  rw [value4, value52, value56, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (39 : Vertex) (303 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 87 = false := by
  rw [value51, value52, value56, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (294 : Vertex) (303 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 173 = true ∨ valuation q 51 = true ∨ valuation q 56 = true ∨ valuation q 87 = true := by
  rw [value51, value52, value56, value87, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (39 : Vertex) → w ∈ [(294 : Vertex), (303 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (39 : Vertex) [(294 : Vertex), (303 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 173 = true ∨ valuation q 4 = true ∨ valuation q 51 = true ∨ valuation q 87 = true := by
  rw [value4, value51, value52, value87, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(39 : Vertex), (294 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (303 : Vertex) [(39 : Vertex), (294 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 174 = true ∨ valuation q 88 = true := by
  rw [value53, value88, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (288 : Vertex) [(424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 174 = true ∨ valuation q 49 = true := by
  rw [value49, value53, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(288 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (424 : Vertex) [(288 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 175 = true ∨ valuation q 71 = true ∨ valuation q 90 = true := by
  rw [value54, value71, value90, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(363 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (303 : Vertex) [(363 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 175 = true ∨ valuation q 56 = true ∨ valuation q 90 = true := by
  rw [value54, value56, value90, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(303 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (363 : Vertex) [(303 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 175 = true ∨ valuation q 56 = true ∨ valuation q 71 = true := by
  rw [value54, value56, value71, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(303 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (427 : Vertex) [(303 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 176 = true ∨ valuation q 56 = true := by
  rw [value55, value56, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(303 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (317 : Vertex) [(303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value52, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 93 = false := by
  rw [value52, value54, value56, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (299 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 93 = false := by
  rw [value52, value55, value56, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (301 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 93 = false := by
  rw [value54, value55, value56, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (299 : Vertex) (301 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 177 = true ∨ valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 93 = true := by
  rw [value52, value54, value56, value93, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (303 : Vertex) w → w ∈ region → w ≠ (301 : Vertex) → w ∈ [(295 : Vertex), (299 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (303 : Vertex) (301 : Vertex) [(295 : Vertex), (299 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 49 = false ∨ valuation q 58 = false ∨ valuation q 61 = false := by
  rw [value49, value57, value58, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (288 : Vertex) (305 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 49 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value49, value57, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (288 : Vertex) (306 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 178 = true ∨ valuation q 58 = true ∨ valuation q 59 = true ∨ valuation q 61 = true := by
  rw [value57, value58, value59, value61, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (304 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(305 : Vertex), (306 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (304 : Vertex) (288 : Vertex) [(305 : Vertex), (306 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 178 = true ∨ valuation q 49 = true ∨ valuation q 59 = true ∨ valuation q 61 = true := by
  rw [value49, value57, value59, value61, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (304 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(288 : Vertex), (306 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (304 : Vertex) (305 : Vertex) [(288 : Vertex), (306 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 178 = true ∨ valuation q 49 = true ∨ valuation q 58 = true ∨ valuation q 61 = true := by
  rw [value49, value57, value58, value61, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (304 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(288 : Vertex), (305 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (304 : Vertex) (306 : Vertex) [(288 : Vertex), (305 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 50 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value50, value57, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (289 : Vertex) (304 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 50 = false ∨ valuation q 57 = false ∨ valuation q 94 = false := by
  rw [value50, value57, value58, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (289 : Vertex) (304 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E026.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112026
