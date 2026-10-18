import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 171 = true ∨ valuation q 48 = true ∨ valuation q 66 = true ∨ valuation q 84 = true := by
  rw [value47, value48, value66, value84, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(259 : Vertex), (322 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (266 : Vertex) [(259 : Vertex), (322 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 85 = false := by
  rw [value47, value48, value53, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (259 : Vertex) (258 : Vertex) (267 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = false ∨ valuation q 67 = false ∨ valuation q 85 = false := by
  rw [value47, value48, value67, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (259 : Vertex) (258 : Vertex) (323 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 67 = false ∨ valuation q 85 = false := by
  rw [value48, value53, value67, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (259 : Vertex) (267 : Vertex) (323 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 53 = true ∨ valuation q 67 = true ∨ valuation q 85 = true := by
  rw [value48, value53, value67, value85, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(267 : Vertex), (323 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (258 : Vertex) [(267 : Vertex), (323 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 47 = true ∨ valuation q 67 = true ∨ valuation q 85 = true := by
  rw [value47, value48, value67, value85, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(258 : Vertex), (323 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (267 : Vertex) [(258 : Vertex), (323 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 47 = true ∨ valuation q 53 = true ∨ valuation q 85 = true := by
  rw [value47, value48, value53, value85, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(258 : Vertex), (267 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (323 : Vertex) [(258 : Vertex), (267 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 47 = true ∨ valuation q 53 = true ∨ valuation q 67 = true := by
  rw [value47, value48, value53, value67, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(258 : Vertex), (267 : Vertex), (323 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (387 : Vertex) [(258 : Vertex), (267 : Vertex), (323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value49, value50, value54, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 49 = false ∨ valuation q 58 = false ∨ valuation q 86 = false := by
  rw [value49, value50, value58, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (260 : Vertex) (277 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 49 = false ∨ valuation q 68 = false ∨ valuation q 86 = false := by
  rw [value49, value50, value68, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (260 : Vertex) (325 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 58 = false ∨ valuation q 68 = false ∨ valuation q 86 = false := by
  rw [value50, value58, value68, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (277 : Vertex) (325 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 175 = true ∨ valuation q 61 = true ∨ valuation q 88 = true := by
  rw [value51, value61, value88, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(281 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (267 : Vertex) [(281 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 175 = true ∨ valuation q 53 = true ∨ valuation q 88 = true := by
  rw [value51, value53, value88, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(267 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (281 : Vertex) [(267 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 175 = true ∨ valuation q 53 = true ∨ valuation q 61 = true := by
  rw [value51, value53, value61, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(267 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (393 : Vertex) [(267 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 55 = false ∨ valuation q 89 = false := by
  rw [value47, value52, value55, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (270 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 89 = true := by
  rw [value52, value53, value55, value89, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(267 : Vertex), (270 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (258 : Vertex) [(267 : Vertex), (270 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 47 = true ∨ valuation q 55 = true ∨ valuation q 89 = true := by
  rw [value47, value52, value55, value89, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(258 : Vertex), (270 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (267 : Vertex) [(258 : Vertex), (270 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 47 = true ∨ valuation q 53 = true ∨ valuation q 89 = true := by
  rw [value47, value52, value53, value89, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(258 : Vertex), (267 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (270 : Vertex) [(258 : Vertex), (267 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 47 = true ∨ valuation q 53 = true ∨ valuation q 55 = true := by
  rw [value47, value52, value53, value55, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(258 : Vertex), (267 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (394 : Vertex) [(258 : Vertex), (267 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value48, value51, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (265 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 62 = false := by
  rw [value48, value51, value53, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (265 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 70 = false := by
  rw [value48, value51, value53, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (265 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 62 = false := by
  rw [value48, value52, value53, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (266 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 70 = false := by
  rw [value48, value52, value53, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (266 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 62 = false ∨ valuation q 70 = false := by
  rw [value48, value53, value62, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (283 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 62 = false := by
  rw [value51, value52, value53, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (265 : Vertex) (266 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 70 = false := by
  rw [value51, value52, value53, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (265 : Vertex) (266 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 70 = false := by
  rw [value51, value53, value62, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (265 : Vertex) (283 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 52 = false ∨ valuation q 62 = false ∨ valuation q 70 = false := by
  rw [value52, value53, value62, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (266 : Vertex) (283 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 55 = true ∨ valuation q 90 = true := by
  rw [value54, value55, value90, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(270 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (260 : Vertex) [(270 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 49 = true ∨ valuation q 90 = true := by
  rw [value49, value54, value90, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(260 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (270 : Vertex) [(260 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E186.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112186
