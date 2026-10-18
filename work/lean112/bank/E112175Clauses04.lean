import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 152 = true ∨ valuation q 50 = true := by
  rw [value48, value50, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(296 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (289 : Vertex) [(296 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 153 = true ∨ valuation q 48 = true := by
  rw [value48, value49, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(288 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (305 : Vertex) [(288 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 154 = true ∨ valuation q 86 = true := by
  rw [value50, value86, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (288 : Vertex) [(424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 155 = true ∨ valuation q 49 = true := by
  rw [value49, value51, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(289 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (307 : Vertex) [(289 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 156 = true ∨ valuation q 53 = true := by
  rw [value52, value53, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (306 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(307 : Vertex)] := by decide
  have hg := other_cover q (306 : Vertex) (310 : Vertex) [(307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 157 = true ∨ valuation q 51 = true := by
  rw [value51, value53, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(305 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (306 : Vertex) [(305 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 158 = true ∨ valuation q 52 = true := by
  rw [value52, value54, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(306 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (318 : Vertex) [(306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 159 = true ∨ valuation q 57 = true := by
  rw [value55, value57, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(318 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (317 : Vertex) [(318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 55 = true := by
  rw [value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ∈ [(316 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (317 : Vertex) [(316 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 56 = true := by
  rw [value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 161 = true ∨ valuation q 54 = true := by
  rw [value54, value57, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (318 : Vertex) w → w ∈ region → w ≠ (316 : Vertex) → w ∈ [(310 : Vertex)] := by decide
  have hg := other_cover q (318 : Vertex) (316 : Vertex) [(310 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 8 = false ∨ valuation q 59 = false ∨ valuation q 62 = false := by
  rw [value8, value58, value59, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (64 : Vertex) (321 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 58 = false ∨ valuation q 66 = false := by
  rw [value9, value58, value59, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (65 : Vertex) (320 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 163 = true ∨ valuation q 9 = true ∨ valuation q 63 = true ∨ valuation q 66 = true := by
  rw [value9, value59, value63, value66, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(65 : Vertex), (329 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(65 : Vertex), (329 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 163 = true ∨ valuation q 9 = true ∨ valuation q 58 = true ∨ valuation q 63 = true := by
  rw [value9, value58, value59, value63, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(65 : Vertex), (320 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (337 : Vertex) [(65 : Vertex), (320 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 11 = false ∨ valuation q 61 = false ∨ valuation q 69 = false := by
  rw [value11, value60, value61, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (70 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 164 = true ∨ valuation q 11 = true ∨ valuation q 69 = true := by
  rw [value11, value60, value69, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(70 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (327 : Vertex) [(70 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 165 = true ∨ valuation q 65 = true := by
  rw [value61, value65, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(335 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 165 = true ∨ valuation q 60 = true := by
  rw [value60, value61, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(326 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (335 : Vertex) [(326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 12 = true ∨ valuation q 58 = true ∨ valuation q 63 = true := by
  rw [value12, value58, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ∈ [(72 : Vertex), (320 : Vertex), (329 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (328 : Vertex) [(72 : Vertex), (320 : Vertex), (329 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 166 = true ∨ valuation q 58 = true ∨ valuation q 63 = true := by
  rw [value58, value62, value63, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(320 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (72 : Vertex) [(320 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 166 = true ∨ valuation q 12 = true ∨ valuation q 63 = true := by
  rw [value12, value62, value63, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(72 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (320 : Vertex) [(72 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value59, value62, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (328 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 72 = false := by
  rw [value63, value64, value65, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (329 : Vertex) (335 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 168 = true ∨ valuation q 63 = true ∨ valuation q 72 = true := by
  rw [value63, value64, value72, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(329 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (335 : Vertex) [(329 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 168 = true ∨ valuation q 63 = true ∨ valuation q 65 = true := by
  rw [value63, value64, value65, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(329 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (349 : Vertex) [(329 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 169 = true ∨ valuation q 61 = true := by
  rw [value61, value65, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(327 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (333 : Vertex) [(327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 170 = true ∨ valuation q 68 = true := by
  rw [value66, value68, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(339 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (321 : Vertex) [(339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 170 = true ∨ valuation q 59 = true := by
  rw [value59, value66, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(321 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (339 : Vertex) [(321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value67, value68, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (339 : Vertex) (342 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 171 = true ∨ valuation q 69 = true ∨ valuation q 70 = true := by
  rw [value67, value69, value70, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(342 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (339 : Vertex) [(342 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 171 = true ∨ valuation q 68 = true ∨ valuation q 69 = true := by
  rw [value67, value68, value69, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(339 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (346 : Vertex) [(339 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E175.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112175
