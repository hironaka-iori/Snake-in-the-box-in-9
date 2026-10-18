import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 154 = true ∨ valuation q 33 = true ∨ valuation q 34 = true := by
  rw [value33, value34, value35, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(153 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (159 : Vertex) [(153 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 155 = true ∨ valuation q 35 = true := by
  rw [value35, value36, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(155 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (151 : Vertex) [(155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 155 = true ∨ valuation q 32 = true := by
  rw [value32, value36, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(151 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (155 : Vertex) [(151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 49 = false := by
  rw [value37, value38, value39, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (194 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 156 = true ∨ valuation q 39 = true ∨ valuation q 49 = true := by
  rw [value37, value39, value49, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(194 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (193 : Vertex) [(194 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 41 = false ∨ valuation q 50 = false := by
  rw [value37, value38, value41, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (192 : Vertex) (197 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value38, value40, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (195 : Vertex) (197 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 50 = false := by
  rw [value38, value41, value43, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (197 : Vertex) (201 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 157 = true ∨ valuation q 40 = true ∨ valuation q 41 = true ∨ valuation q 43 = true ∨ valuation q 50 = true := by
  rw [value38, value40, value41, value43, value50, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(195 : Vertex), (197 : Vertex), (201 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (192 : Vertex) [(195 : Vertex), (197 : Vertex), (201 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 157 = true ∨ valuation q 37 = true ∨ valuation q 41 = true ∨ valuation q 43 = true ∨ valuation q 50 = true := by
  rw [value37, value38, value41, value43, value50, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(192 : Vertex), (197 : Vertex), (201 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (195 : Vertex) [(192 : Vertex), (197 : Vertex), (201 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 157 = true ∨ valuation q 37 = true ∨ valuation q 40 = true ∨ valuation q 43 = true ∨ valuation q 50 = true := by
  rw [value37, value38, value40, value43, value50, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(192 : Vertex), (195 : Vertex), (201 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (197 : Vertex) [(192 : Vertex), (195 : Vertex), (201 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 157 = true ∨ valuation q 37 = true ∨ valuation q 40 = true ∨ valuation q 41 = true ∨ valuation q 50 = true := by
  rw [value37, value38, value40, value41, value50, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(192 : Vertex), (195 : Vertex), (197 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (201 : Vertex) [(192 : Vertex), (195 : Vertex), (197 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 157 = true ∨ valuation q 37 = true ∨ valuation q 40 = true ∨ valuation q 41 = true ∨ valuation q 43 = true := by
  rw [value37, value38, value40, value41, value43, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(192 : Vertex), (195 : Vertex), (197 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (209 : Vertex) [(192 : Vertex), (195 : Vertex), (197 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 19 = false ∨ valuation q 40 = false := by
  rw [value1, value19, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (130 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 19 = false ∨ valuation q 51 = false := by
  rw [value1, value19, value39, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (130 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 19 = false ∨ valuation q 102 = false := by
  rw [value1, value19, value39, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (130 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 37 = false ∨ valuation q 40 = false := by
  rw [value1, value37, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (192 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 37 = false ∨ valuation q 51 = false := by
  rw [value1, value37, value39, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (192 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 37 = false ∨ valuation q 102 = false := by
  rw [value1, value37, value39, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (192 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 40 = false ∨ valuation q 44 = false := by
  rw [value1, value39, value40, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (195 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 40 = false ∨ valuation q 51 = false := by
  rw [value1, value39, value40, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (195 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 40 = false ∨ valuation q 102 = false := by
  rw [value1, value39, value40, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (195 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 51 = false ∨ valuation q 102 = false := by
  rw [value1, value39, value51, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (210 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 37 = false ∨ valuation q 51 = false ∨ valuation q 102 = false := by
  rw [value37, value39, value51, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (192 : Vertex) (210 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 44 = false ∨ valuation q 51 = false ∨ valuation q 102 = false := by
  rw [value39, value44, value51, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (202 : Vertex) (210 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 20 = false ∨ valuation q 38 = false := by
  rw [value2, value20, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (131 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 20 = false ∨ valuation q 39 = false := by
  rw [value2, value20, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (131 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 20 = false ∨ valuation q 42 = false := by
  rw [value2, value20, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (131 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 20 = false ∨ valuation q 52 = false := by
  rw [value2, value20, value40, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (131 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 20 = false ∨ valuation q 103 = false := by
  rw [value2, value20, value40, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (131 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 38 = false ∨ valuation q 42 = false := by
  rw [value2, value38, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (193 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 2 = false ∨ valuation q 38 = false ∨ valuation q 52 = false := by
  rw [value2, value38, value40, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (193 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E078.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112078
