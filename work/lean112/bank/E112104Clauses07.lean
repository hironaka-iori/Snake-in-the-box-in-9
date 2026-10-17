import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 75 = true ∨ valuation q 78 = true := by
  rw [value75, value77, value78, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (382 : Vertex) w → w ∈ region → w ≠ (374 : Vertex) → w ∈ [(378 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (382 : Vertex) (374 : Vertex) [(378 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 74 = true ∨ valuation q 78 = true := by
  rw [value74, value77, value78, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (382 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(374 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (382 : Vertex) (378 : Vertex) [(374 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 118 = false := by
  rw [value76, value77, value78, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (381 : Vertex) (382 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 196 = true ∨ valuation q 77 = true ∨ valuation q 118 = true := by
  rw [value77, value78, value118, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (381 : Vertex) → w ∈ [(382 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (381 : Vertex) [(382 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 196 = true ∨ valuation q 76 = true ∨ valuation q 118 = true := by
  rw [value76, value78, value118, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (382 : Vertex) → w ∈ [(381 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (382 : Vertex) [(381 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 89 = false := by
  rw [value79, value80, value82, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (419 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 79 = false ∨ valuation q 85 = false ∨ valuation q 98 = false := by
  rw [value79, value80, value85, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (417 : Vertex) (427 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 198 = true ∨ valuation q 83 = true ∨ valuation q 85 = true ∨ valuation q 98 = true := by
  rw [value80, value83, value85, value98, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(423 : Vertex), (427 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (417 : Vertex) [(423 : Vertex), (427 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 199 = true ∨ valuation q 82 = true ∨ valuation q 99 = true := by
  rw [value81, value82, value99, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(421 : Vertex), (484 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (428 : Vertex) [(421 : Vertex), (484 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 202 = true ∨ valuation q 92 = true ∨ valuation q 104 = true := by
  rw [value84, value92, value104, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(442 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (427 : Vertex) [(442 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 202 = true ∨ valuation q 85 = true ∨ valuation q 104 = true := by
  rw [value84, value85, value104, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(427 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (442 : Vertex) [(427 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 202 = true ∨ valuation q 85 = true ∨ valuation q 92 = true := by
  rw [value84, value85, value92, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(427 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (490 : Vertex) [(427 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 105 = false := by
  rw [value80, value84, value85, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (419 : Vertex) (426 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 203 = true ∨ valuation q 84 = true ∨ valuation q 105 = true := by
  rw [value84, value85, value105, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(426 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (419 : Vertex) [(426 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 203 = true ∨ valuation q 80 = true ∨ valuation q 105 = true := by
  rw [value80, value85, value105, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(419 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (426 : Vertex) [(419 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 204 = true ∨ valuation q 87 = true ∨ valuation q 106 = true := by
  rw [value86, value87, value106, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(429 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (420 : Vertex) [(429 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 204 = true ∨ valuation q 81 = true ∨ valuation q 106 = true := by
  rw [value81, value86, value106, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (429 : Vertex) → w ∈ [(420 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (429 : Vertex) [(420 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 82 = false ∨ valuation q 86 = false ∨ valuation q 93 = false := by
  rw [value82, value86, value87, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (429 : Vertex) (421 : Vertex) (428 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 82 = false ∨ valuation q 86 = false ∨ valuation q 107 = false := by
  rw [value82, value86, value87, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (429 : Vertex) (421 : Vertex) (428 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 82 = false ∨ valuation q 93 = false ∨ valuation q 107 = false := by
  rw [value82, value87, value93, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (429 : Vertex) (421 : Vertex) (445 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 93 = false ∨ valuation q 107 = false := by
  rw [value86, value87, value93, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (429 : Vertex) (428 : Vertex) (445 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 205 = true ∨ valuation q 82 = true ∨ valuation q 93 = true ∨ valuation q 107 = true := by
  rw [value82, value87, value93, value107, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(421 : Vertex), (445 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (428 : Vertex) [(421 : Vertex), (445 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 206 = true ∨ valuation q 90 = true := by
  rw [value88, value90, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(434 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (433 : Vertex) [(434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 88 = true := by
  rw [value88, value89, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(432 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (417 : Vertex) [(432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 79 = true := by
  rw [value79, value89, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(417 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (432 : Vertex) [(417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 208 = true ∨ valuation q 91 = true ∨ valuation q 92 = true := by
  rw [value90, value91, value92, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(438 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (432 : Vertex) [(438 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 90 = false ∨ valuation q 94 = false ∨ valuation q 112 = false := by
  rw [value90, value91, value94, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (438 : Vertex) (434 : Vertex) (446 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 84 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value84, value90, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (434 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 87 = false ∨ valuation q 95 = false ∨ valuation q 117 = false := by
  rw [value87, value93, value95, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (445 : Vertex) (429 : Vertex) (447 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 95 = true ∨ valuation q 117 = true := by
  rw [value93, value95, value117, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (445 : Vertex) w → w ∈ region → w ≠ (429 : Vertex) → w ∈ [(447 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (445 : Vertex) (429 : Vertex) [(447 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 87 = true ∨ valuation q 117 = true := by
  rw [value87, value93, value117, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (445 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(429 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (445 : Vertex) (447 : Vertex) [(429 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 92 = true ∨ valuation q 95 = true := by
  rw [value92, value94, value95, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (438 : Vertex) → w ∈ [(442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (438 : Vertex) [(442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E104.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112104
