import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 138 = true ∨ valuation q 34 = true := by
  rw [value33, value34, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(143 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (137 : Vertex) [(143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 138 = true ∨ valuation q 32 = true := by
  rw [value32, value33, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(137 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (143 : Vertex) [(137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 7 = false ∨ valuation q 33 = false ∨ valuation q 39 = false := by
  rw [value7, value33, value34, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (15 : Vertex) (139 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 7 = false ∨ valuation q 33 = false ∨ valuation q 52 = false := by
  rw [value7, value33, value34, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (15 : Vertex) (139 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 7 = false ∨ valuation q 39 = false ∨ valuation q 52 = false := by
  rw [value7, value34, value39, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (15 : Vertex) (175 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 33 = false ∨ valuation q 39 = false ∨ valuation q 52 = false := by
  rw [value33, value34, value39, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (139 : Vertex) (175 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 139 = true ∨ valuation q 33 = true ∨ valuation q 39 = true ∨ valuation q 52 = true := by
  rw [value33, value34, value39, value52, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(139 : Vertex), (175 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (15 : Vertex) [(139 : Vertex), (175 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 140 = true ∨ valuation q 30 = true ∨ valuation q 73 = true := by
  rw [value30, value35, value73, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(129 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (177 : Vertex) [(129 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 141 = true := by
  rw [value36, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (168 : Vertex) (170 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 142 = true ∨ valuation q 36 = true ∨ valuation q 42 = true := by
  rw [value36, value37, value42, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(168 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (174 : Vertex) [(168 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 142 = true ∨ valuation q 36 = true ∨ valuation q 38 = true := by
  rw [value36, value37, value38, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(168 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (186 : Vertex) [(168 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 80 = false := by
  rw [value37, value38, value39, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (170 : Vertex) (175 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 143 = true ∨ valuation q 37 = true ∨ valuation q 39 = true := by
  rw [value37, value38, value39, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(170 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (174 : Vertex) (430 : Vertex) [(170 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 144 = true ∨ valuation q 38 = true ∨ valuation q 81 = true := by
  rw [value38, value39, value81, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(174 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (143 : Vertex) [(174 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 144 = true ∨ valuation q 34 = true ∨ valuation q 81 = true := by
  rw [value34, value39, value81, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(143 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (174 : Vertex) [(143 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 144 = true ∨ valuation q 34 = true ∨ valuation q 38 = true := by
  rw [value34, value38, value39, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(143 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (431 : Vertex) [(143 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 145 = true ∨ valuation q 41 = true := by
  rw [value40, value41, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(185 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (161 : Vertex) [(185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 145 = true ∨ valuation q 35 = true := by
  rw [value35, value40, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(161 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (185 : Vertex) [(161 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 40 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value40, value41, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (177 : Vertex) (187 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 146 = true ∨ valuation q 43 = true ∨ valuation q 44 = true := by
  rw [value41, value43, value44, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(187 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (177 : Vertex) [(187 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 146 = true ∨ valuation q 40 = true ∨ valuation q 44 = true := by
  rw [value40, value41, value44, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(177 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (187 : Vertex) [(177 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 37 = false ∨ valuation q 43 = false ∨ valuation q 86 = false := by
  rw [value37, value42, value43, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (186 : Vertex) (170 : Vertex) (187 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 147 = true ∨ valuation q 43 = true ∨ valuation q 86 = true := by
  rw [value42, value43, value86, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(187 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (170 : Vertex) [(187 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 147 = true ∨ valuation q 37 = true ∨ valuation q 86 = true := by
  rw [value37, value42, value86, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(170 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (187 : Vertex) [(170 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 148 = true ∨ valuation q 42 = true := by
  rw [value42, value43, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(186 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (185 : Vertex) [(186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 148 = true ∨ valuation q 41 = true := by
  rw [value41, value43, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(185 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (186 : Vertex) [(185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 149 = true ∨ valuation q 88 = true := by
  rw [value44, value88, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(445 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (185 : Vertex) [(445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 150 = true ∨ valuation q 46 = true := by
  rw [value45, value46, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(193 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (200 : Vertex) [(193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 154 = true ∨ valuation q 45 = true := by
  rw [value45, value49, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(192 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (202 : Vertex) [(192 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 155 = true ∨ valuation q 49 = true ∨ valuation q 51 = true := by
  rw [value49, value50, value51, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(200 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (218 : Vertex) [(200 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 52 = false := by
  rw [value47, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (202 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 157 = true ∨ valuation q 34 = true ∨ valuation q 51 = true := by
  rw [value34, value51, value52, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(143 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (199 : Vertex) [(143 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E075.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112075
