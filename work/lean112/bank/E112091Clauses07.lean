import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 171 = true ∨ valuation q 59 = true ∨ valuation q 64 = true := by
  rw [value59, value64, value65, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(238 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (255 : Vertex) [(238 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 172 = true ∨ valuation q 65 = true := by
  rw [value65, value66, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(254 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (251 : Vertex) [(254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 172 = true ∨ valuation q 63 = true := by
  rw [value63, value66, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(251 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (254 : Vertex) [(251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 173 = true ∨ valuation q 4 = true := by
  rw [value4, value67, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(8 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (296 : Vertex) [(8 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 68 = true := by
  rw [value68, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (296 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 72 = false ∨ valuation q 80 = false := by
  rw [value72, value80, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (296 : Vertex) (360 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 174 = true ∨ valuation q 67 = true ∨ valuation q 80 = true := by
  rw [value67, value68, value80, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(264 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (360 : Vertex) [(264 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 175 = true ∨ valuation q 73 = true := by
  rw [value69, value73, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (353 : Vertex) w → w ∈ region → w ≠ (357 : Vertex) → w ∈ [(361 : Vertex)] := by decide
  have hg := other_cover q (353 : Vertex) (357 : Vertex) [(361 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 176 = true ∨ valuation q 69 = true := by
  rw [value69, value70, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(353 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (359 : Vertex) [(353 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 177 = true ∨ valuation q 70 = true := by
  rw [value70, value71, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (359 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(357 : Vertex)] := by decide
  have hg := other_cover q (359 : Vertex) (367 : Vertex) [(357 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 178 = true ∨ valuation q 68 = true := by
  rw [value68, value72, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(296 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (361 : Vertex) [(296 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 179 = true ∨ valuation q 72 = true := by
  rw [value72, value73, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (353 : Vertex) → w ∈ [(360 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (353 : Vertex) [(360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = true := by
  rw [value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ∈ [(367 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (366 : Vertex) [(367 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 74 = true := by
  rw [value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 181 = true ∨ valuation q 71 = true := by
  rw [value71, value75, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(359 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (366 : Vertex) [(359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 34 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value34, value76, value80, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (424 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value76, value77, value80, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (424 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 182 = true ∨ valuation q 77 = true ∨ valuation q 80 = true ∨ valuation q 84 = true := by
  rw [value76, value77, value80, value84, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(417 : Vertex), (424 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (160 : Vertex) [(417 : Vertex), (424 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 182 = true ∨ valuation q 34 = true ∨ valuation q 80 = true ∨ valuation q 84 = true := by
  rw [value34, value76, value80, value84, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(160 : Vertex), (424 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (417 : Vertex) [(160 : Vertex), (424 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 81 = false := by
  rw [value76, value77, value78, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (421 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 183 = true ∨ valuation q 76 = true ∨ valuation q 81 = true := by
  rw [value76, value77, value81, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(416 : Vertex), (425 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (421 : Vertex) [(416 : Vertex), (425 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 184 = true ∨ valuation q 77 = true := by
  rw [value77, value78, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(417 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (423 : Vertex) [(417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 185 = true ∨ valuation q 78 = true := by
  rw [value78, value79, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (423 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(421 : Vertex)] := by decide
  have hg := other_cover q (423 : Vertex) (431 : Vertex) [(421 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 37 = false ∨ valuation q 68 = false ∨ valuation q 76 = false := by
  rw [value37, value68, value76, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 37 = false ∨ valuation q 68 = false ∨ valuation q 81 = false := by
  rw [value37, value68, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 68 = false ∨ valuation q 76 = false ∨ valuation q 81 = false := by
  rw [value68, value76, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (416 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 38 = false ∨ valuation q 77 = false ∨ valuation q 80 = false := by
  rw [value38, value77, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (169 : Vertex) (417 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 187 = true ∨ valuation q 77 = true ∨ valuation q 80 = true := by
  rw [value77, value80, value81, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(417 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (169 : Vertex) [(417 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 187 = true ∨ valuation q 38 = true ∨ valuation q 80 = true := by
  rw [value38, value80, value81, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(169 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (417 : Vertex) [(169 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 41 = false ∨ valuation q 83 = false ∨ valuation q 89 = false := by
  rw [value41, value82, value83, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (431 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 189 = true ∨ valuation q 79 = true ∨ valuation q 90 = true := by
  rw [value79, value83, value90, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(423 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (430 : Vertex) [(423 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 189 = true ∨ valuation q 79 = true ∨ valuation q 82 = true := by
  rw [value79, value82, value83, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(423 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (447 : Vertex) [(423 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E091.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112091
