import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 57 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value57, value90, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (423 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 57 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value57, value90, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (423 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 57 = false ∨ valuation q 93 = false ∨ valuation q 95 = false := by
  rw [value57, value93, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (427 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 95 = false := by
  rw [value90, value93, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (423 : Vertex) (427 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 213 = true ∨ valuation q 84 = true ∨ valuation q 100 = true ∨ valuation q 102 = true := by
  rw [value84, value97, value100, value102, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(416 : Vertex), (436 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (434 : Vertex) [(416 : Vertex), (436 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 213 = true ∨ valuation q 84 = true ∨ valuation q 98 = true ∨ valuation q 102 = true := by
  rw [value84, value97, value98, value102, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(416 : Vertex), (434 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (436 : Vertex) [(416 : Vertex), (434 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 213 = true ∨ valuation q 84 = true ∨ valuation q 98 = true ∨ valuation q 100 = true := by
  rw [value84, value97, value98, value100, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(416 : Vertex), (434 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (440 : Vertex) [(416 : Vertex), (434 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 86 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value86, value97, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (418 : Vertex) (432 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value97, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (432 : Vertex) (435 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 215 = true ∨ valuation q 98 = true := by
  rw [value98, value99, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(434 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (419 : Vertex) [(434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 215 = true ∨ valuation q 87 = true := by
  rw [value87, value99, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(419 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (434 : Vertex) [(419 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 42 = false ∨ valuation q 59 = false ∨ valuation q 103 = false := by
  rw [value42, value59, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (180 : Vertex) (308 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 42 = false ∨ valuation q 59 = false ∨ valuation q 114 = false := by
  rw [value42, value59, value100, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (180 : Vertex) (308 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value97, value100, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (432 : Vertex) (438 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value97, value100, value101, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (432 : Vertex) (438 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 97 = false ∨ valuation q 103 = false ∨ valuation q 114 = false := by
  rw [value97, value100, value103, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (432 : Vertex) (444 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 114 = false := by
  rw [value100, value101, value103, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (438 : Vertex) (444 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 91 = false ∨ valuation q 97 = false ∨ valuation q 103 = false := by
  rw [value91, value97, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (424 : Vertex) (432 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 222 = true ∨ valuation q 67 = true ∨ valuation q 85 = true := by
  rw [value67, value85, value106, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(353 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (497 : Vertex) [(353 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 86 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value86, value107, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (418 : Vertex) (486 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 223 = true ∨ valuation q 86 = true ∨ valuation q 108 = true := by
  rw [value86, value107, value108, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(418 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (490 : Vertex) [(418 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 91 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value91, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (490 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 226 = true ∨ valuation q 91 = true ∨ valuation q 112 = true := by
  rw [value91, value110, value112, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(424 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (490 : Vertex) [(424 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 226 = true ∨ valuation q 91 = true ∨ valuation q 111 = true := by
  rw [value91, value110, value111, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(424 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (492 : Vertex) [(424 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 227 = true ∨ valuation q 110 = true := by
  rw [value110, value111, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(488 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (482 : Vertex) [(488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 227 = true ∨ valuation q 107 = true := by
  rw [value107, value111, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(482 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (488 : Vertex) [(482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 228 = true ∨ valuation q 110 = true := by
  rw [value110, value112, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(488 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (428 : Vertex) [(488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 228 = true ∨ valuation q 94 = true := by
  rw [value94, value112, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(428 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (488 : Vertex) [(428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 106 = true ∨ valuation q 115 = true := by
  rw [value106, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ∈ [(481 : Vertex), (501 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (497 : Vertex) [(481 : Vertex), (501 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 113 = true := by
  rw [value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 230 = true ∨ valuation q 100 = true ∨ valuation q 116 = true := by
  rw [value100, value114, value116, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (501 : Vertex) → w ∈ [(436 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (501 : Vertex) [(436 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 231 = true ∨ valuation q 114 = true := by
  rw [value114, value115, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (501 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(500 : Vertex)] := by decide
  have hg := other_cover q (501 : Vertex) (497 : Vertex) [(500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E051.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112051
