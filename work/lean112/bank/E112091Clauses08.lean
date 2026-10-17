import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 76 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value76, value84, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (434 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 190 = true ∨ valuation q 76 = true ∨ valuation q 87 = true := by
  rw [value76, value84, value87, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(416 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (434 : Vertex) [(416 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 190 = true ∨ valuation q 76 = true ∨ valuation q 85 = true := by
  rw [value76, value84, value85, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(416 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (436 : Vertex) [(416 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 84 = true ∨ valuation q 86 = true := by
  rw [value84, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ∈ [(432 : Vertex), (435 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (434 : Vertex) [(432 : Vertex), (435 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value84, value86, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (434 : Vertex) (432 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 191 = true ∨ valuation q 86 = true := by
  rw [value85, value86, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(435 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (432 : Vertex) [(435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 191 = true ∨ valuation q 84 = true := by
  rw [value84, value85, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(432 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (435 : Vertex) [(432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 192 = true ∨ valuation q 85 = true := by
  rw [value85, value86, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(434 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (179 : Vertex) [(434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 192 = true ∨ valuation q 42 = true := by
  rw [value42, value86, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(179 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (434 : Vertex) [(179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 43 = false ∨ valuation q 84 = false ∨ valuation q 88 = false := by
  rw [value43, value84, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (180 : Vertex) (432 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 193 = true ∨ valuation q 43 = true ∨ valuation q 84 = true := by
  rw [value43, value84, value87, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (444 : Vertex) → w ∈ [(180 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (444 : Vertex) [(180 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 194 = true ∨ valuation q 87 = true := by
  rw [value87, value88, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(436 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (446 : Vertex) [(436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 195 = true ∨ valuation q 88 = true ∨ valuation q 90 = true := by
  rw [value88, value89, value90, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(444 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (430 : Vertex) [(444 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 195 = true ∨ valuation q 82 = true ∨ valuation q 88 = true := by
  rw [value82, value88, value89, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(430 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (447 : Vertex) [(430 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 196 = true ∨ valuation q 83 = true := by
  rw [value83, value90, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(431 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (446 : Vertex) [(431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 99 = false := by
  rw [value91, value92, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (449 : Vertex) (456 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 93 = false ∨ valuation q 96 = false := by
  rw [value91, value92, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (453 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 198 = true ∨ valuation q 91 = true ∨ valuation q 96 = true := by
  rw [value91, value92, value96, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(448 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (453 : Vertex) [(448 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 198 = true ∨ valuation q 91 = true ∨ valuation q 93 = true := by
  rw [value91, value92, value93, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(448 : Vertex), (453 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (457 : Vertex) [(448 : Vertex), (453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 199 = true ∨ valuation q 94 = true := by
  rw [value93, value94, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(455 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (449 : Vertex) [(455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 199 = true ∨ valuation q 92 = true := by
  rw [value92, value93, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(449 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (455 : Vertex) [(449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 200 = true ∨ valuation q 98 = true := by
  rw [value94, value98, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(463 : Vertex)] := by decide
  have hg := other_cover q (455 : Vertex) (453 : Vertex) [(463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 200 = true ∨ valuation q 93 = true := by
  rw [value93, value94, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(453 : Vertex)] := by decide
  have hg := other_cover q (455 : Vertex) (463 : Vertex) [(453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 52 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value52, value91, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (448 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 201 = true ∨ valuation q 52 = true ∨ valuation q 91 = true := by
  rw [value52, value91, value95, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (456 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(200 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (456 : Vertex) (457 : Vertex) [(200 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 202 = true ∨ valuation q 95 = true := by
  rw [value95, value96, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(456 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (449 : Vertex) [(456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 202 = true ∨ valuation q 92 = true := by
  rw [value92, value96, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(449 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (456 : Vertex) [(449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 203 = true ∨ valuation q 98 = true := by
  rw [value97, value98, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(463 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (478 : Vertex) [(463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 204 = true ∨ valuation q 94 = true ∨ valuation q 106 = true := by
  rw [value94, value98, value106, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(455 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (462 : Vertex) [(455 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 91 = false ∨ valuation q 100 = false ∨ valuation q 102 = false := by
  rw [value91, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 205 = true ∨ valuation q 91 = true ∨ valuation q 102 = true := by
  rw [value91, value99, value102, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(448 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (466 : Vertex) [(448 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 205 = true ∨ valuation q 91 = true ∨ valuation q 100 = true := by
  rw [value91, value99, value100, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(448 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (468 : Vertex) [(448 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E091.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112091
