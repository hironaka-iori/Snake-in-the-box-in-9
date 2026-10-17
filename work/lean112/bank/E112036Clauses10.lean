import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 27 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value27, value64, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (122 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 27 = false ∨ valuation q 64 = false ∨ valuation q 125 = false := by
  rw [value27, value64, value66, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (122 : Vertex) (248 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 27 = false ∨ valuation q 67 = false ∨ valuation q 125 = false := by
  rw [value27, value66, value67, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (122 : Vertex) (251 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 57 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value57, value64, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 57 = false ∨ valuation q 64 = false ∨ valuation q 125 = false := by
  rw [value57, value64, value66, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (248 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 57 = false ∨ valuation q 67 = false ∨ valuation q 125 = false := by
  rw [value57, value66, value67, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (251 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 125 = false := by
  rw [value64, value66, value67, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (248 : Vertex) (251 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 58 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value58, value65, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (249 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 58 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value58, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (250 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value65, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (249 : Vertex) (250 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 195 = true ∨ valuation q 65 = true ∨ valuation q 66 = true ∨ valuation q 68 = true := by
  rw [value65, value66, value67, value68, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(249 : Vertex), (250 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (235 : Vertex) [(249 : Vertex), (250 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 195 = true ∨ valuation q 58 = true ∨ valuation q 66 = true ∨ valuation q 68 = true := by
  rw [value58, value66, value67, value68, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(235 : Vertex), (250 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (249 : Vertex) [(235 : Vertex), (250 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 195 = true ∨ valuation q 58 = true ∨ valuation q 65 = true ∨ valuation q 68 = true := by
  rw [value58, value65, value67, value68, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(235 : Vertex), (249 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (250 : Vertex) [(235 : Vertex), (249 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 195 = true ∨ valuation q 58 = true ∨ valuation q 65 = true ∨ valuation q 66 = true := by
  rw [value58, value65, value66, value67, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(235 : Vertex), (249 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (255 : Vertex) [(235 : Vertex), (249 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 68 = true := by
  rw [value68, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (255 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 50 = true ∨ valuation q 63 = true ∨ valuation q 67 = true := by
  rw [value50, value63, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ∈ [(191 : Vertex), (247 : Vertex), (251 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (255 : Vertex) [(191 : Vertex), (247 : Vertex), (251 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 50 = false ∨ valuation q 63 = false ∨ valuation q 67 = false := by
  rw [value50, value63, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (191 : Vertex) (247 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 50 = false ∨ valuation q 63 = false := by
  rw [value50, value63, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (255 : Vertex) (191 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 63 = false ∨ valuation q 67 = false := by
  rw [value63, value67, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (255 : Vertex) (247 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 196 = true ∨ valuation q 50 = true ∨ valuation q 67 = true := by
  rw [value50, value67, value68, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(191 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (247 : Vertex) [(191 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 196 = true ∨ valuation q 50 = true ∨ valuation q 63 = true := by
  rw [value50, value63, value68, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(191 : Vertex), (247 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (251 : Vertex) [(191 : Vertex), (247 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 88 = false := by
  rw [value69, value70, value73, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 197 = true ∨ valuation q 73 = true ∨ valuation q 88 = true := by
  rw [value69, value73, value88, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(296 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (289 : Vertex) [(296 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 197 = true ∨ valuation q 70 = true ∨ valuation q 88 = true := by
  rw [value69, value70, value88, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(289 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (296 : Vertex) [(289 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 78 = false ∨ valuation q 89 = false := by
  rw [value69, value70, value78, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (288 : Vertex) (305 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 78 = false ∨ valuation q 89 = false := by
  rw [value70, value74, value78, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (297 : Vertex) (305 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 198 = true ∨ valuation q 74 = true ∨ valuation q 78 = true ∨ valuation q 89 = true := by
  rw [value70, value74, value78, value89, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(297 : Vertex), (305 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (288 : Vertex) [(297 : Vertex), (305 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 198 = true ∨ valuation q 69 = true ∨ valuation q 78 = true ∨ valuation q 89 = true := by
  rw [value69, value70, value78, value89, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(288 : Vertex), (305 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (297 : Vertex) [(288 : Vertex), (305 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 198 = true ∨ valuation q 69 = true ∨ valuation q 74 = true ∨ valuation q 89 = true := by
  rw [value69, value70, value74, value89, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(288 : Vertex), (297 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (305 : Vertex) [(288 : Vertex), (297 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 198 = true ∨ valuation q 69 = true ∨ valuation q 74 = true ∨ valuation q 78 = true := by
  rw [value69, value70, value74, value78, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(288 : Vertex), (297 : Vertex), (305 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (417 : Vertex) [(288 : Vertex), (297 : Vertex), (305 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 82 = false ∨ valuation q 93 = false := by
  rw [value71, value72, value82, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (295 : Vertex) (310 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 71 = true ∨ valuation q 77 = true ∨ valuation q 94 = true := by
  rw [value71, value72, value77, value94, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (39 : Vertex) → w ∈ [(294 : Vertex), (303 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (39 : Vertex) [(294 : Vertex), (303 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E036.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112036
