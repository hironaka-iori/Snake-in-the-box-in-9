import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 169 = true ∨ valuation q 40 = true ∨ valuation q 48 = true := by
  rw [value40, value47, value48, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(228 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (180 : Vertex) [(228 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 169 = true ∨ valuation q 32 = true ∨ valuation q 40 = true := by
  rw [value32, value40, value47, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(180 : Vertex), (228 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (245 : Vertex) [(180 : Vertex), (228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 41 = false ∨ valuation q 47 = false ∨ valuation q 49 = false := by
  rw [value41, value47, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (229 : Vertex) (244 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 170 = true ∨ valuation q 41 = true ∨ valuation q 47 = true := by
  rw [value41, value47, value48, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(229 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (245 : Vertex) (247 : Vertex) [(229 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 171 = true ∨ valuation q 54 = true := by
  rw [value49, value54, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (245 : Vertex) [(255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 171 = true ∨ valuation q 48 = true := by
  rw [value48, value49, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(245 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (255 : Vertex) [(245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 172 = true ∨ valuation q 52 = true ∨ valuation q 118 = true := by
  rw [value50, value52, value118, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(250 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (249 : Vertex) [(250 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 172 = true ∨ valuation q 51 = true ∨ valuation q 118 = true := by
  rw [value50, value51, value118, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(249 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (250 : Vertex) [(249 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 172 = true ∨ valuation q 51 = true ∨ valuation q 52 = true := by
  rw [value50, value51, value52, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(249 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (504 : Vertex) [(249 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 50 = false ∨ valuation q 53 = false := by
  rw [value50, value53, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (249 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 173 = true ∨ valuation q 53 = true := by
  rw [value51, value53, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(251 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (248 : Vertex) [(251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 34 = false ∨ valuation q 43 = false ∨ valuation q 50 = false := by
  rw [value34, value43, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (186 : Vertex) (234 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 34 = false ∨ valuation q 43 = false ∨ valuation q 53 = false := by
  rw [value34, value43, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (186 : Vertex) (234 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 34 = false ∨ valuation q 50 = false ∨ valuation q 53 = false := by
  rw [value34, value50, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (186 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 43 = false ∨ valuation q 50 = false ∨ valuation q 53 = false := by
  rw [value43, value50, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 174 = true ∨ valuation q 34 = true ∨ valuation q 43 = true ∨ valuation q 53 = true := by
  rw [value34, value43, value52, value53, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (250 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(186 : Vertex), (234 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (250 : Vertex) (248 : Vertex) [(186 : Vertex), (234 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 44 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value44, value51, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (249 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 44 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value44, value52, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (250 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value51, value52, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (249 : Vertex) (250 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 122 = false := by
  rw [value49, value53, value54, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (247 : Vertex) (251 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 176 = true ∨ valuation q 53 = true ∨ valuation q 122 = true := by
  rw [value53, value54, value122, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(251 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (247 : Vertex) [(251 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 64 = false := by
  rw [value55, value56, value60, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (304 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 72 = false := by
  rw [value55, value56, value60, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (352 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 80 = false := by
  rw [value55, value56, value60, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 64 = false ∨ valuation q 72 = false := by
  rw [value55, value56, value64, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (304 : Vertex) (352 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 64 = false ∨ valuation q 80 = false := by
  rw [value55, value56, value64, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (304 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 72 = false ∨ valuation q 80 = false := by
  rw [value55, value56, value72, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (352 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 60 = false ∨ valuation q 64 = false ∨ valuation q 72 = false := by
  rw [value55, value60, value64, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (296 : Vertex) (304 : Vertex) (352 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 60 = false ∨ valuation q 64 = false ∨ valuation q 80 = false := by
  rw [value55, value60, value64, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (296 : Vertex) (304 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 60 = false ∨ valuation q 72 = false ∨ valuation q 80 = false := by
  rw [value55, value60, value72, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (296 : Vertex) (352 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 64 = false ∨ valuation q 72 = false ∨ valuation q 80 = false := by
  rw [value55, value64, value72, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (304 : Vertex) (352 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value56, value60, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.First112
