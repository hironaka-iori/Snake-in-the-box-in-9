import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 32 = true ∨ valuation q 36 = true ∨ valuation q 87 = true := by
  rw [value32, value33, value36, value87, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(160 : Vertex), (165 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (33 : Vertex) [(160 : Vertex), (165 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 1 = true ∨ valuation q 36 = true ∨ valuation q 87 = true := by
  rw [value1, value33, value36, value87, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(33 : Vertex), (165 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (160 : Vertex) [(33 : Vertex), (165 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 1 = true ∨ valuation q 32 = true ∨ valuation q 87 = true := by
  rw [value1, value32, value33, value87, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(33 : Vertex), (160 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (165 : Vertex) [(33 : Vertex), (160 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 1 = true ∨ valuation q 32 = true ∨ valuation q 36 = true := by
  rw [value1, value32, value33, value36, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(33 : Vertex), (160 : Vertex), (165 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (417 : Vertex) [(33 : Vertex), (160 : Vertex), (165 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 32 = false ∨ valuation q 37 = false := by
  rw [value2, value32, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (160 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 32 = false ∨ valuation q 39 = false := by
  rw [value2, value32, value34, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (160 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 32 = false ∨ valuation q 43 = false := by
  rw [value2, value32, value34, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (160 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 37 = false ∨ valuation q 39 = false := by
  rw [value2, value34, value37, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (166 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 37 = false ∨ valuation q 52 = false := by
  rw [value2, value34, value37, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (166 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 37 = false ∨ valuation q 88 = false := by
  rw [value2, value34, value37, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (166 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 39 = false ∨ valuation q 43 = false := by
  rw [value2, value34, value39, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (170 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 39 = false ∨ valuation q 52 = false := by
  rw [value2, value34, value39, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (170 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 43 = false ∨ valuation q 52 = false := by
  rw [value2, value34, value43, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (178 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 39 = false := by
  rw [value32, value34, value37, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (166 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 52 = false := by
  rw [value32, value34, value37, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (166 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 43 = false := by
  rw [value32, value34, value39, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (170 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 52 = false := by
  rw [value32, value34, value39, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (170 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 88 = false := by
  rw [value32, value34, value39, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (170 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 43 = false ∨ valuation q 52 = false := by
  rw [value32, value34, value43, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (178 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 43 = false ∨ valuation q 88 = false := by
  rw [value32, value34, value43, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (178 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 52 = false := by
  rw [value34, value37, value39, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (166 : Vertex) (170 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 88 = false := by
  rw [value34, value37, value39, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (166 : Vertex) (170 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 43 = false ∨ valuation q 88 = false := by
  rw [value34, value37, value43, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (166 : Vertex) (178 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 52 = false ∨ valuation q 88 = false := by
  rw [value34, value37, value52, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (166 : Vertex) (226 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 39 = false ∨ valuation q 43 = false ∨ valuation q 52 = false := by
  rw [value34, value39, value43, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (170 : Vertex) (178 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 39 = false ∨ valuation q 43 = false ∨ valuation q 88 = false := by
  rw [value34, value39, value43, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (170 : Vertex) (178 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 158 = true ∨ valuation q 32 = true ∨ valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 43 = true ∨ valuation q 52 = true ∨ valuation q 88 = true := by
  rw [value32, value34, value37, value39, value43, value52, value88, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (34 : Vertex) → w ∈ [(160 : Vertex), (166 : Vertex), (170 : Vertex), (178 : Vertex), (226 : Vertex), (418 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (34 : Vertex) [(160 : Vertex), (166 : Vertex), (170 : Vertex), (178 : Vertex), (226 : Vertex), (418 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 158 = true ∨ valuation q 2 = true ∨ valuation q 32 = true ∨ valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 43 = true ∨ valuation q 88 = true := by
  rw [value2, value32, value34, value37, value39, value43, value88, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(34 : Vertex), (160 : Vertex), (166 : Vertex), (170 : Vertex), (178 : Vertex), (418 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (226 : Vertex) [(34 : Vertex), (160 : Vertex), (166 : Vertex), (170 : Vertex), (178 : Vertex), (418 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 32 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value32, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (164 : Vertex) (160 : Vertex) (165 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 41 = false := by
  rw [value35, value36, value37, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (164 : Vertex) (165 : Vertex) (166 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 159 = true ∨ valuation q 36 = true ∨ valuation q 37 = true ∨ valuation q 41 = true := by
  rw [value35, value36, value37, value41, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(165 : Vertex), (166 : Vertex), (172 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (160 : Vertex) [(165 : Vertex), (166 : Vertex), (172 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 159 = true ∨ valuation q 32 = true ∨ valuation q 37 = true ∨ valuation q 41 = true := by
  rw [value32, value35, value37, value41, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(160 : Vertex), (166 : Vertex), (172 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (165 : Vertex) [(160 : Vertex), (166 : Vertex), (172 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E008.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112008
