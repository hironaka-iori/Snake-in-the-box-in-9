import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 150 = true ∨ valuation q 20 = true ∨ valuation q 31 = true := by
  rw [value20, value29, value31, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(173 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (188 : Vertex) [(173 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value26, value28, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value26, value28, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (190 : Vertex) (182 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 26 = false ∨ valuation q 31 = false := by
  rw [value26, value31, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (190 : Vertex) (182 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 151 = true ∨ valuation q 28 = true ∨ valuation q 31 = true := by
  rw [value28, value30, value31, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(188 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (182 : Vertex) [(188 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 21 = false ∨ valuation q 29 = false ∨ valuation q 48 = false := by
  rw [value21, value29, value31, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (189 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 21 = false ∨ valuation q 30 = false ∨ valuation q 48 = false := by
  rw [value21, value30, value31, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (190 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 48 = false := by
  rw [value29, value30, value31, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (189 : Vertex) (190 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 14 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value14, value32, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (227 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 14 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value14, value32, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 14 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value14, value32, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (230 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value32, value33, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (227 : Vertex) (230 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 153 = true ∨ valuation q 33 = true ∨ valuation q 36 = true ∨ valuation q 37 = true := by
  rw [value32, value33, value36, value37, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(227 : Vertex), (230 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (226 : Vertex) (162 : Vertex) [(227 : Vertex), (230 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 153 = true ∨ valuation q 14 = true ∨ valuation q 36 = true ∨ valuation q 37 = true := by
  rw [value14, value32, value36, value37, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(162 : Vertex), (230 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (226 : Vertex) (227 : Vertex) [(162 : Vertex), (230 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 154 = true ∨ valuation q 15 = true ∨ valuation q 32 = true ∨ valuation q 38 = true := by
  rw [value15, value32, value33, value38, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(163 : Vertex), (226 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (99 : Vertex) [(163 : Vertex), (226 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 154 = true ∨ valuation q 9 = true ∨ valuation q 32 = true ∨ valuation q 38 = true := by
  rw [value9, value32, value33, value38, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(99 : Vertex), (226 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (163 : Vertex) [(99 : Vertex), (226 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 154 = true ∨ valuation q 9 = true ∨ valuation q 15 = true ∨ valuation q 38 = true := by
  rw [value9, value15, value33, value38, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(99 : Vertex), (163 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (226 : Vertex) [(99 : Vertex), (163 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 10 = false ∨ valuation q 35 = false ∨ valuation q 39 = false := by
  rw [value10, value34, value35, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (100 : Vertex) (229 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 10 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value10, value34, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (100 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 39 = false := by
  rw [value34, value35, value36, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 41 = false := by
  rw [value34, value35, value36, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value34, value35, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value34, value36, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (230 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 16 = false ∨ valuation q 34 = false ∨ valuation q 42 = false := by
  rw [value16, value34, value35, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (165 : Vertex) (228 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 156 = true ∨ valuation q 16 = true ∨ valuation q 42 = true := by
  rw [value16, value35, value42, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(165 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (228 : Vertex) [(165 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 156 = true ∨ valuation q 16 = true ∨ valuation q 34 = true := by
  rw [value16, value34, value35, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(165 : Vertex), (228 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (245 : Vertex) [(165 : Vertex), (228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 17 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value17, value32, value34, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (230 : Vertex) (166 : Vertex) (226 : Vertex) (228 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 158 = true ∨ valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 46 = true := by
  rw [value37, value38, value40, value46, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(235 : Vertex), (238 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (226 : Vertex) [(235 : Vertex), (238 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 158 = true ∨ valuation q 32 = true ∨ valuation q 38 = true ∨ valuation q 46 = true := by
  rw [value32, value37, value38, value46, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(226 : Vertex), (235 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (238 : Vertex) [(226 : Vertex), (235 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 19 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value19, value33, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 19 = false ∨ valuation q 33 = false ∨ valuation q 47 = false := by
  rw [value19, value33, value38, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 19 = false ∨ valuation q 33 = false ∨ valuation q 110 = false := by
  rw [value19, value33, value38, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E024.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112024
