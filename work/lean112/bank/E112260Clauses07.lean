import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 159 = true ∨ valuation q 33 = true ∨ valuation q 70 = true := by
  rw [value32, value33, value70, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (120 : Vertex) w → w ∈ region → w ≠ (104 : Vertex) → w ∈ [(122 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (120 : Vertex) (104 : Vertex) [(122 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 159 = true ∨ valuation q 23 = true ∨ valuation q 70 = true := by
  rw [value23, value32, value70, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (120 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(104 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (120 : Vertex) (122 : Vertex) [(104 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 159 = true ∨ valuation q 23 = true ∨ valuation q 33 = true := by
  rw [value23, value32, value33, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (120 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(104 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (120 : Vertex) (248 : Vertex) [(104 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 160 = true ∨ valuation q 32 = true := by
  rw [value32, value33, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(120 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (90 : Vertex) [(120 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 160 = true ∨ valuation q 16 = true := by
  rw [value16, value33, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(90 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (120 : Vertex) [(90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 34 = true := by
  rw [value34, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (125 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 17 = true ∨ valuation q 35 = true := by
  rw [value17, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ∈ [(93 : Vertex), (127 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (125 : Vertex) [(93 : Vertex), (127 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 17 = false ∨ valuation q 35 = false := by
  rw [value17, value35, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (125 : Vertex) (93 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 161 = true ∨ valuation q 35 = true := by
  rw [value34, value35, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (93 : Vertex) → w ∈ [(127 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (93 : Vertex) [(127 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 161 = true ∨ valuation q 17 = true := by
  rw [value17, value34, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (127 : Vertex) → w ∈ [(93 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (127 : Vertex) [(93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 162 = true ∨ valuation q 73 = true := by
  rw [value35, value73, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (127 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(255 : Vertex)] := by decide
  have hg := other_cover q (127 : Vertex) (125 : Vertex) [(255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 162 = true ∨ valuation q 34 = true := by
  rw [value34, value35, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (127 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (127 : Vertex) (255 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 36 = true := by
  rw [value36, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (192 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value36, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (194 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 47 = false := by
  rw [value36, value37, value38, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (194 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 55 = false := by
  rw [value36, value37, value38, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (194 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 163 = true ∨ valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 47 = true ∨ valuation q 55 = true ∨ valuation q 102 = true := by
  rw [value36, value38, value39, value47, value55, value102, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(194 : Vertex), (196 : Vertex), (208 : Vertex), (224 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (193 : Vertex) [(194 : Vertex), (196 : Vertex), (208 : Vertex), (224 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 163 = true ∨ valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 47 = true ∨ valuation q 55 = true := by
  rw [value36, value37, value38, value39, value47, value55, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(193 : Vertex), (194 : Vertex), (196 : Vertex), (208 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (448 : Vertex) [(193 : Vertex), (194 : Vertex), (196 : Vertex), (208 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 1 = false ∨ valuation q 36 = false ∨ valuation q 40 = false := by
  rw [value1, value36, value37, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (192 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 1 = false ∨ valuation q 36 = false ∨ valuation q 48 = false := by
  rw [value1, value36, value37, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (192 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 1 = false ∨ valuation q 40 = false ∨ valuation q 48 = false := by
  rw [value1, value37, value40, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (197 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 1 = false ∨ valuation q 48 = false ∨ valuation q 103 = false := by
  rw [value1, value37, value48, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (209 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 48 = false := by
  rw [value36, value37, value40, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (192 : Vertex) (197 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 103 = false := by
  rw [value36, value37, value40, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (192 : Vertex) (197 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 36 = false ∨ valuation q 48 = false ∨ valuation q 103 = false := by
  rw [value36, value37, value48, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (192 : Vertex) (209 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 164 = true ∨ valuation q 36 = true ∨ valuation q 40 = true ∨ valuation q 48 = true ∨ valuation q 103 = true := by
  rw [value36, value37, value40, value48, value103, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(192 : Vertex), (197 : Vertex), (209 : Vertex), (449 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (65 : Vertex) [(192 : Vertex), (197 : Vertex), (209 : Vertex), (449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 164 = true ∨ valuation q 1 = true ∨ valuation q 36 = true ∨ valuation q 40 = true ∨ valuation q 103 = true := by
  rw [value1, value36, value37, value40, value103, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(65 : Vertex), (192 : Vertex), (197 : Vertex), (449 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (209 : Vertex) [(65 : Vertex), (192 : Vertex), (197 : Vertex), (449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 164 = true ∨ valuation q 1 = true ∨ valuation q 36 = true ∨ valuation q 40 = true ∨ valuation q 48 = true := by
  rw [value1, value36, value37, value40, value48, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(65 : Vertex), (192 : Vertex), (197 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (449 : Vertex) [(65 : Vertex), (192 : Vertex), (197 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 2 = false ∨ valuation q 36 = false ∨ valuation q 42 = false := by
  rw [value2, value36, value38, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (192 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 2 = false ∨ valuation q 36 = false ∨ valuation q 49 = false := by
  rw [value2, value36, value38, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (192 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 2 = false ∨ valuation q 36 = false ∨ valuation q 56 = false := by
  rw [value2, value36, value38, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (192 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 2 = false ∨ valuation q 42 = false ∨ valuation q 49 = false := by
  rw [value2, value38, value42, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (202 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E260.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112260
