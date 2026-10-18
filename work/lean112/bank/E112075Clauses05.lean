import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 199 = true ∨ valuation q 95 = true := by
  rw [value94, value95, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(490 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (480 : Vertex) [(490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 200 = true ∨ valuation q 96 = true ∨ valuation q 103 = true := by
  rw [value95, value96, value103, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(494 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (488 : Vertex) [(494 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 200 = true ∨ valuation q 94 = true ∨ valuation q 96 = true := by
  rw [value94, value95, value96, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(488 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (506 : Vertex) [(488 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 80 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value80, value92, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (430 : Vertex) (486 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 80 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value80, value92, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (430 : Vertex) (486 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 80 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value80, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (430 : Vertex) (490 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value92, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (486 : Vertex) (490 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 202 = true ∨ valuation q 81 = true ∨ valuation q 93 = true ∨ valuation q 96 = true := by
  rw [value81, value93, value96, value97, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(431 : Vertex), (487 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (367 : Vertex) [(431 : Vertex), (487 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 202 = true ∨ valuation q 68 = true ∨ valuation q 81 = true ∨ valuation q 96 = true := by
  rw [value68, value81, value96, value97, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(367 : Vertex), (431 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (487 : Vertex) [(367 : Vertex), (431 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 91 = false ∨ valuation q 100 = false ∨ valuation q 102 = false := by
  rw [value91, value98, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (481 : Vertex) (501 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 204 = true ∨ valuation q 100 = true := by
  rw [value99, value100, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(501 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (502 : Vertex) [(501 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 105 = false := by
  rw [value98, value99, value100, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (497 : Vertex) (500 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 206 = true ∨ valuation q 99 = true := by
  rw [value99, value101, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(500 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (486 : Vertex) [(500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 207 = true ∨ valuation q 98 = true ∨ valuation q 105 = true := by
  rw [value98, value102, value105, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(497 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (507 : Vertex) [(497 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 86 = false ∨ valuation q 95 = false ∨ valuation q 104 = false := by
  rw [value86, value95, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (506 : Vertex) (442 : Vertex) (490 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 208 = true ∨ valuation q 86 = true ∨ valuation q 104 = true := by
  rw [value86, value103, value104, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(442 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (490 : Vertex) [(442 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 208 = true ∨ valuation q 86 = true ∨ valuation q 95 = true := by
  rw [value86, value95, value103, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(442 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (507 : Vertex) [(442 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 209 = true ∨ valuation q 103 = true := by
  rw [value103, value104, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (505 : Vertex) → w ∈ [(506 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (505 : Vertex) [(506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 209 = true ∨ valuation q 102 = true := by
  rw [value102, value104, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(505 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (506 : Vertex) [(505 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 88 = false ∨ valuation q 100 = false ∨ valuation q 102 = false := by
  rw [value88, value100, value102, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (445 : Vertex) (501 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 106 = false := by
  rw [value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (0 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 108 = false := by
  rw [value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (6 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 111 = false := by
  rw [value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (10 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 112 = false := by
  rw [value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (15 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 113 = false := by
  rw [value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (20 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 118 = false := by
  rw [value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (27 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 119 = false := by
  rw [value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (29 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 120 = false := by
  rw [value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (96 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 127 = false := by
  rw [value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (111 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 138 = false := by
  rw [value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (139 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 142 = false := by
  rw [value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (170 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 144 = false := by
  rw [value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (175 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block5 (q : Snake 81) (h : Conditions q) : B112E075.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112075
