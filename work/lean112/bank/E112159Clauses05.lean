import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 104 = false := by
  rw [value34, value41, value45, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (237 : Vertex) (245 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 36 = false ∨ valuation q 46 = false := by
  rw [value15, value35, value36, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (230 : Vertex) (166 : Vertex) (231 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 154 = true ∨ valuation q 34 = true ∨ valuation q 35 = true ∨ valuation q 42 = true ∨ valuation q 47 = true := by
  rw [value34, value35, value36, value42, value47, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (231 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(229 : Vertex), (230 : Vertex), (239 : Vertex), (247 : Vertex)] := by decide
  have hg := other_cover q (231 : Vertex) (227 : Vertex) [(229 : Vertex), (230 : Vertex), (239 : Vertex), (247 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 38 = false ∨ valuation q 40 = false := by
  rw [value16, value37, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (168 : Vertex) (233 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 38 = false ∨ valuation q 48 = false := by
  rw [value16, value37, value38, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (168 : Vertex) (233 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 40 = false ∨ valuation q 48 = false := by
  rw [value16, value37, value40, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (168 : Vertex) (236 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 155 = true ∨ valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 48 = true := by
  rw [value37, value38, value40, value48, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(233 : Vertex), (236 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (168 : Vertex) [(233 : Vertex), (236 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 155 = true ∨ valuation q 16 = true ∨ valuation q 40 = true ∨ valuation q 48 = true := by
  rw [value16, value37, value40, value48, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(168 : Vertex), (236 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (233 : Vertex) [(168 : Vertex), (236 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 155 = true ∨ valuation q 16 = true ∨ valuation q 38 = true ∨ valuation q 40 = true := by
  rw [value16, value37, value38, value40, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(168 : Vertex), (233 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (248 : Vertex) [(168 : Vertex), (233 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 39 = false := by
  rw [value32, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (225 : Vertex) (232 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 41 = false := by
  rw [value32, value37, value38, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (225 : Vertex) (232 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 49 = false := by
  rw [value32, value37, value38, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (225 : Vertex) (232 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value32, value38, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (225 : Vertex) (235 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 49 = false := by
  rw [value32, value38, value39, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (225 : Vertex) (235 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 41 = false ∨ valuation q 49 = false := by
  rw [value32, value38, value41, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (225 : Vertex) (237 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value37, value38, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (232 : Vertex) (235 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 49 = false := by
  rw [value37, value38, value39, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (232 : Vertex) (235 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 49 = false := by
  rw [value38, value39, value41, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (235 : Vertex) (237 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 17 = false ∨ valuation q 33 = false ∨ valuation q 107 = false := by
  rw [value17, value33, value39, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 17 = false ∨ valuation q 38 = false ∨ valuation q 107 = false := by
  rw [value17, value38, value39, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (233 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 33 = true ∨ valuation q 38 = true ∨ valuation q 42 = true ∨ valuation q 107 = true := by
  rw [value33, value38, value39, value42, value107, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(227 : Vertex), (233 : Vertex), (239 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (171 : Vertex) [(227 : Vertex), (233 : Vertex), (239 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 17 = true ∨ valuation q 33 = true ∨ valuation q 38 = true ∨ valuation q 42 = true := by
  rw [value17, value33, value38, value39, value42, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (491 : Vertex) → w ∈ [(171 : Vertex), (227 : Vertex), (233 : Vertex), (239 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (491 : Vertex) [(171 : Vertex), (227 : Vertex), (233 : Vertex), (239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 18 = false ∨ valuation q 37 = false := by
  rw [value5, value18, value37, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (172 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 18 = false ∨ valuation q 41 = false := by
  rw [value5, value18, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (172 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 18 = false ∨ valuation q 51 = false := by
  rw [value5, value18, value40, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (172 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 18 = false ∨ valuation q 108 = false := by
  rw [value5, value18, value40, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (172 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 37 = false ∨ valuation q 41 = false := by
  rw [value5, value37, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (232 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 37 = false ∨ valuation q 51 = false := by
  rw [value5, value37, value40, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (232 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 37 = false ∨ valuation q 108 = false := by
  rw [value5, value37, value40, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (232 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 41 = false ∨ valuation q 51 = false := by
  rw [value5, value40, value41, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (237 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 51 = false ∨ valuation q 108 = false := by
  rw [value5, value40, value51, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (252 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 18 = false ∨ valuation q 37 = false ∨ valuation q 41 = false := by
  rw [value18, value37, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (172 : Vertex) (232 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E159.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112159
