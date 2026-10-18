import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 67 = false := by
  rw [value10, value19, value29, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (57 : Vertex) (105 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 10 = false ∨ valuation q 25 = false ∨ valuation q 67 = false := by
  rw [value10, value25, value29, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (57 : Vertex) (113 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 67 = false := by
  rw [value19, value25, value29, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (105 : Vertex) (113 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 153 = true ∨ valuation q 19 = true ∨ valuation q 25 = true ∨ valuation q 67 = true := by
  rw [value19, value25, value29, value67, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (121 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(105 : Vertex), (113 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (121 : Vertex) (57 : Vertex) [(105 : Vertex), (113 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 153 = true ∨ valuation q 10 = true ∨ valuation q 25 = true ∨ valuation q 67 = true := by
  rw [value10, value25, value29, value67, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (121 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(57 : Vertex), (113 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (121 : Vertex) (105 : Vertex) [(57 : Vertex), (113 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 153 = true ∨ valuation q 10 = true ∨ valuation q 19 = true ∨ valuation q 67 = true := by
  rw [value10, value19, value29, value67, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (121 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(57 : Vertex), (105 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (121 : Vertex) (113 : Vertex) [(57 : Vertex), (105 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 153 = true ∨ valuation q 10 = true ∨ valuation q 19 = true ∨ valuation q 25 = true := by
  rw [value10, value19, value25, value29, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (121 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(57 : Vertex), (105 : Vertex), (113 : Vertex)] := by decide
  have hg := other_cover q (121 : Vertex) (249 : Vertex) [(57 : Vertex), (105 : Vertex), (113 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 26 = false ∨ valuation q 32 = false := by
  rw [value11, value26, value30, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (122 : Vertex) (58 : Vertex) (114 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 32 = false ∨ valuation q 82 = false := by
  rw [value11, value30, value32, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (122 : Vertex) (58 : Vertex) (126 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 26 = false ∨ valuation q 32 = false ∨ valuation q 82 = false := by
  rw [value26, value30, value32, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (122 : Vertex) (114 : Vertex) (126 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 154 = true ∨ valuation q 26 = true ∨ valuation q 32 = true ∨ valuation q 82 = true := by
  rw [value26, value30, value32, value82, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(114 : Vertex), (126 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (58 : Vertex) [(114 : Vertex), (126 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 154 = true ∨ valuation q 11 = true ∨ valuation q 32 = true ∨ valuation q 82 = true := by
  rw [value11, value30, value32, value82, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(58 : Vertex), (126 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (114 : Vertex) [(58 : Vertex), (126 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 154 = true ∨ valuation q 11 = true ∨ valuation q 26 = true ∨ valuation q 82 = true := by
  rw [value11, value26, value30, value82, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(58 : Vertex), (114 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (126 : Vertex) [(58 : Vertex), (114 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 154 = true ∨ valuation q 11 = true ∨ valuation q 26 = true ∨ valuation q 32 = true := by
  rw [value11, value26, value30, value32, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(58 : Vertex), (114 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (378 : Vertex) [(58 : Vertex), (114 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 32 = false := by
  rw [value20, value28, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (124 : Vertex) (108 : Vertex) (116 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 155 = true ∨ valuation q 28 = true ∨ valuation q 32 = true := by
  rw [value28, value31, value32, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(116 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (108 : Vertex) [(116 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 155 = true ∨ valuation q 20 = true ∨ valuation q 32 = true := by
  rw [value20, value31, value32, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (116 : Vertex) → w ∈ [(108 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (116 : Vertex) [(108 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 155 = true ∨ valuation q 20 = true ∨ valuation q 28 = true := by
  rw [value20, value28, value31, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(108 : Vertex), (116 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (126 : Vertex) [(108 : Vertex), (116 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value22, value30, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (110 : Vertex) (122 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 156 = true ∨ valuation q 22 = true ∨ valuation q 31 = true := by
  rw [value22, value31, value32, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(110 : Vertex), (124 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (122 : Vertex) [(110 : Vertex), (124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 156 = true ∨ valuation q 22 = true ∨ valuation q 30 = true := by
  rw [value22, value30, value32, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(110 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (124 : Vertex) [(110 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 35 = true ∨ valuation q 42 = true := by
  rw [value33, value35, value42, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(162 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (161 : Vertex) [(162 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 34 = true ∨ valuation q 42 = true := by
  rw [value33, value34, value42, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(161 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (162 : Vertex) [(161 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 158 = true ∨ valuation q 33 = true ∨ valuation q 36 = true ∨ valuation q 43 = true ∨ valuation q 86 = true := by
  rw [value33, value34, value36, value43, value86, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (177 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (225 : Vertex) [(160 : Vertex), (163 : Vertex), (177 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 158 = true ∨ valuation q 33 = true ∨ valuation q 36 = true ∨ valuation q 43 = true ∨ valuation q 51 = true := by
  rw [value33, value34, value36, value43, value51, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (177 : Vertex), (225 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (417 : Vertex) [(160 : Vertex), (163 : Vertex), (177 : Vertex), (225 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 159 = true ∨ valuation q 36 = true := by
  rw [value35, value36, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(163 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (160 : Vertex) [(163 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 159 = true ∨ valuation q 33 = true := by
  rw [value33, value35, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(160 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (163 : Vertex) [(160 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 38 = false := by
  rw [value34, value35, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (162 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value34, value36, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (167 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 35 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value35, value36, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (162 : Vertex) (167 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 160 = true ∨ valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 38 = true := by
  rw [value34, value36, value37, value38, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (163 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(161 : Vertex), (167 : Vertex), (171 : Vertex)] := by decide
  have hg := other_cover q (163 : Vertex) (162 : Vertex) [(161 : Vertex), (167 : Vertex), (171 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 36 = false ∨ valuation q 41 = false ∨ valuation q 89 = false := by
  rw [value36, value37, value41, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (167 : Vertex) (163 : Vertex) (175 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E020.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112020
