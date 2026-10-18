import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 12 = false ∨ valuation q 29 = false ∨ valuation q 33 = false := by
  rw [value12, value29, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (300 : Vertex) (268 : Vertex) (296 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 12 = false ∨ valuation q 29 = false ∨ valuation q 90 = false := by
  rw [value12, value29, value32, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (300 : Vertex) (268 : Vertex) (296 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 12 = false ∨ valuation q 33 = false ∨ valuation q 90 = false := by
  rw [value12, value32, value33, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (300 : Vertex) (268 : Vertex) (302 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 29 = false ∨ valuation q 33 = false ∨ valuation q 90 = false := by
  rw [value29, value32, value33, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (300 : Vertex) (296 : Vertex) (302 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 12 = false ∨ valuation q 33 = false := by
  rw [value12, value33, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (300 : Vertex) (268 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 154 = true ∨ valuation q 29 = true ∨ valuation q 33 = true ∨ valuation q 90 = true := by
  rw [value29, value32, value33, value90, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (300 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(296 : Vertex), (302 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (300 : Vertex) (268 : Vertex) [(296 : Vertex), (302 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 154 = true ∨ valuation q 12 = true ∨ valuation q 29 = true ∨ valuation q 90 = true := by
  rw [value12, value29, value32, value90, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (300 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(268 : Vertex), (296 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (300 : Vertex) (302 : Vertex) [(268 : Vertex), (296 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 155 = true ∨ valuation q 32 = true ∨ valuation q 92 = true := by
  rw [value32, value33, value92, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(300 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (294 : Vertex) [(300 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 155 = true ∨ valuation q 27 = true ∨ valuation q 92 = true := by
  rw [value27, value33, value92, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(294 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (300 : Vertex) [(294 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 155 = true ∨ valuation q 27 = true ∨ valuation q 32 = true := by
  rw [value27, value32, value33, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(294 : Vertex), (300 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (430 : Vertex) [(294 : Vertex), (300 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 15 = false ∨ valuation q 35 = false ∨ valuation q 93 = false := by
  rw [value15, value34, value35, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (273 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 156 = true ∨ valuation q 15 = true ∨ valuation q 93 = true := by
  rw [value15, value34, value93, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(273 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (307 : Vertex) [(273 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 16 = false ∨ valuation q 34 = false ∨ valuation q 95 = false := by
  rw [value16, value34, value35, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (275 : Vertex) (305 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 157 = true ∨ valuation q 34 = true ∨ valuation q 95 = true := by
  rw [value34, value35, value95, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(305 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (275 : Vertex) [(305 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 157 = true ∨ valuation q 16 = true ∨ valuation q 95 = true := by
  rw [value16, value35, value95, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(275 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(275 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 157 = true ∨ valuation q 16 = true ∨ valuation q 34 = true := by
  rw [value16, value34, value35, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(275 : Vertex), (305 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (435 : Vertex) [(275 : Vertex), (305 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 158 = true ∨ valuation q 37 = true := by
  rw [value36, value37, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (308 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(310 : Vertex)] := by decide
  have hg := other_cover q (308 : Vertex) (276 : Vertex) [(310 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 158 = true ∨ valuation q 17 = true := by
  rw [value17, value36, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (308 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(276 : Vertex)] := by decide
  have hg := other_cover q (308 : Vertex) (310 : Vertex) [(276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 27 = false ∨ valuation q 36 = false ∨ valuation q 97 = false := by
  rw [value27, value36, value37, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (310 : Vertex) (294 : Vertex) (308 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 159 = true ∨ valuation q 36 = true ∨ valuation q 97 = true := by
  rw [value36, value37, value97, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(308 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (294 : Vertex) [(308 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 159 = true ∨ valuation q 27 = true ∨ valuation q 97 = true := by
  rw [value27, value37, value97, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(294 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (308 : Vertex) [(294 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 159 = true ∨ valuation q 27 = true ∨ valuation q 36 = true := by
  rw [value27, value36, value37, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (438 : Vertex) → w ∈ [(294 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (438 : Vertex) [(294 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 29 = false ∨ valuation q 39 = false ∨ valuation q 98 = false := by
  rw [value29, value38, value39, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (312 : Vertex) (296 : Vertex) (314 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 160 = true ∨ valuation q 29 = true ∨ valuation q 98 = true := by
  rw [value29, value38, value98, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (312 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(296 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (312 : Vertex) (314 : Vertex) [(296 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 160 = true ∨ valuation q 29 = true ∨ valuation q 39 = true := by
  rw [value29, value38, value39, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (312 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(296 : Vertex), (314 : Vertex)] := by decide
  have hg := other_cover q (312 : Vertex) (440 : Vertex) [(296 : Vertex), (314 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 161 = true ∨ valuation q 38 = true := by
  rw [value38, value39, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(312 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (282 : Vertex) [(312 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 161 = true ∨ valuation q 20 = true := by
  rw [value20, value39, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (312 : Vertex) → w ∈ [(282 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (312 : Vertex) [(282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 21 = false ∨ valuation q 41 = false := by
  rw [value21, value41, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (317 : Vertex) (285 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 162 = true ∨ valuation q 41 = true := by
  rw [value40, value41, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (285 : Vertex) → w ∈ [(319 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (285 : Vertex) [(319 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 162 = true ∨ valuation q 21 = true := by
  rw [value21, value40, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (319 : Vertex) → w ∈ [(285 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (319 : Vertex) [(285 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 163 = true ∨ valuation q 40 = true ∨ valuation q 101 = true := by
  rw [value40, value41, value101, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (319 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(317 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (319 : Vertex) (287 : Vertex) [(317 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 163 = true ∨ valuation q 23 = true ∨ valuation q 101 = true := by
  rw [value23, value41, value101, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (319 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(287 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (319 : Vertex) (317 : Vertex) [(287 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E258.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112258
