import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 42 = false ∨ valuation q 46 = false ∨ valuation q 49 = false := by
  rw [value42, value46, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (241 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 163 = true ∨ valuation q 42 = true ∨ valuation q 49 = true := by
  rw [value42, value47, value49, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(241 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (248 : Vertex) [(241 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 163 = true ∨ valuation q 42 = true ∨ valuation q 46 = true := by
  rw [value42, value46, value47, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(241 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (251 : Vertex) [(241 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 49 = false := by
  rw [value38, value46, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 38 = false ∨ valuation q 49 = false ∨ valuation q 113 = false := by
  rw [value38, value48, value49, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (251 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 113 = false := by
  rw [value46, value48, value49, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (248 : Vertex) (251 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 38 = true ∨ valuation q 46 = true ∨ valuation q 49 = true := by
  rw [value38, value46, value48, value49, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (250 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(234 : Vertex), (248 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (250 : Vertex) (506 : Vertex) [(234 : Vertex), (248 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 39 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value39, value47, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (249 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 39 = false ∨ valuation q 48 = false ∨ valuation q 50 = false := by
  rw [value39, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (250 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 165 = true ∨ valuation q 47 = true ∨ valuation q 48 = true ∨ valuation q 50 = true := by
  rw [value47, value48, value49, value50, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(249 : Vertex), (250 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (235 : Vertex) [(249 : Vertex), (250 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 165 = true ∨ valuation q 39 = true ∨ valuation q 48 = true ∨ valuation q 50 = true := by
  rw [value39, value48, value49, value50, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(235 : Vertex), (250 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (249 : Vertex) [(235 : Vertex), (250 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 165 = true ∨ valuation q 39 = true ∨ valuation q 47 = true ∨ valuation q 50 = true := by
  rw [value39, value47, value49, value50, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(235 : Vertex), (249 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (250 : Vertex) [(235 : Vertex), (249 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 165 = true ∨ valuation q 39 = true ∨ valuation q 47 = true ∨ valuation q 48 = true := by
  rw [value39, value47, value48, value49, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(235 : Vertex), (249 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (255 : Vertex) [(235 : Vertex), (249 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 30 = false ∨ valuation q 45 = false ∨ valuation q 49 = false := by
  rw [value30, value45, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (191 : Vertex) (247 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 166 = true ∨ valuation q 30 = true ∨ valuation q 49 = true := by
  rw [value30, value49, value50, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(191 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (247 : Vertex) [(191 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 166 = true ∨ valuation q 30 = true ∨ valuation q 45 = true := by
  rw [value30, value45, value50, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(191 : Vertex), (247 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (251 : Vertex) [(191 : Vertex), (247 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 167 = true ∨ valuation q 62 = true := by
  rw [value51, value62, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(291 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (267 : Vertex) [(291 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 167 = true ∨ valuation q 53 = true := by
  rw [value51, value53, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (291 : Vertex) → w ∈ [(267 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (291 : Vertex) [(267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 168 = true ∨ valuation q 56 = true := by
  rw [value52, value56, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (5 : Vertex) → w ∈ [(277 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (5 : Vertex) [(277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 168 = true ∨ valuation q 3 = true := by
  rw [value3, value52, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(5 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (277 : Vertex) [(5 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 4 = false ∨ valuation q 51 = false ∨ valuation q 59 = false := by
  rw [value4, value51, value53, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (259 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 169 = true ∨ valuation q 51 = true ∨ valuation q 59 = true := by
  rw [value51, value53, value59, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(259 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (11 : Vertex) [(259 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 169 = true ∨ valuation q 4 = true ∨ valuation q 59 = true := by
  rw [value4, value53, value59, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(11 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (259 : Vertex) [(11 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 170 = true ∨ valuation q 63 = true := by
  rw [value54, value63, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(304 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (276 : Vertex) [(304 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 170 = true ∨ valuation q 55 = true := by
  rw [value54, value55, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (304 : Vertex) → w ∈ [(276 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (304 : Vertex) [(276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 171 = true ∨ valuation q 56 = true := by
  rw [value55, value56, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(277 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (272 : Vertex) [(277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 171 = true ∨ valuation q 54 = true := by
  rw [value54, value55, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(272 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (277 : Vertex) [(272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value52, value55, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (261 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 172 = true ∨ valuation q 55 = true ∨ valuation q 57 = true := by
  rw [value55, value56, value57, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(276 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (261 : Vertex) [(276 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 172 = true ∨ valuation q 52 = true ∨ valuation q 57 = true := by
  rw [value52, value56, value57, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(261 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (276 : Vertex) [(261 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 172 = true ∨ valuation q 52 = true ∨ valuation q 55 = true := by
  rw [value52, value55, value56, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(261 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (279 : Vertex) [(261 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 57 = true := by
  rw [value57, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (279 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem block8 (q : Snake 81) (h : Conditions q) : B112E169.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112169
