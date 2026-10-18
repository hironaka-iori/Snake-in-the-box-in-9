import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 65 = false := by
  rw [value57, value58, value61, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (353 : Vertex) (360 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 158 = true ∨ valuation q 57 = true ∨ valuation q 62 = true := by
  rw [value57, value58, value62, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (353 : Vertex) w → w ∈ region → w ≠ (357 : Vertex) → w ∈ [(352 : Vertex), (361 : Vertex)] := by decide
  have hg := other_cover q (353 : Vertex) (357 : Vertex) [(352 : Vertex), (361 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 160 = true ∨ valuation q 64 = true := by
  rw [value60, value64, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (359 : Vertex) w → w ∈ region → w ≠ (357 : Vertex) → w ∈ [(367 : Vertex)] := by decide
  have hg := other_cover q (359 : Vertex) (357 : Vertex) [(367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 161 = true ∨ valuation q 8 = true ∨ valuation q 57 = true := by
  rw [value8, value57, value61, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(104 : Vertex), (352 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (361 : Vertex) [(104 : Vertex), (352 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 162 = true ∨ valuation q 61 = true := by
  rw [value61, value62, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (353 : Vertex) → w ∈ [(360 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (353 : Vertex) [(360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 163 = true ∨ valuation q 70 = true := by
  rw [value63, value70, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(382 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (367 : Vertex) [(382 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 164 = true ∨ valuation q 63 = true := by
  rw [value63, value64, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(366 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (359 : Vertex) [(366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 57 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value57, value65, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (352 : Vertex) (370 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 166 = true ∨ valuation q 65 = true := by
  rw [value65, value66, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(368 : Vertex)] := by decide
  have hg := other_cover q (370 : Vertex) (371 : Vertex) [(368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 66 = true := by
  rw [value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ∈ [(370 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (371 : Vertex) [(370 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 67 = true := by
  rw [value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 169 = true ∨ valuation q 68 = true := by
  rw [value68, value69, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (380 : Vertex) w → w ∈ region → w ≠ (382 : Vertex) → w ∈ [(372 : Vertex)] := by decide
  have hg := other_cover q (380 : Vertex) (382 : Vertex) [(372 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 170 = true ∨ valuation q 69 = true := by
  rw [value69, value70, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (382 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(380 : Vertex)] := by decide
  have hg := other_cover q (382 : Vertex) (366 : Vertex) [(380 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 46 = false ∨ valuation q 73 = false ∨ valuation q 77 = false := by
  rw [value46, value71, value73, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (264 : Vertex) (408 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 46 = false ∨ valuation q 73 = false ∨ valuation q 90 = false := by
  rw [value46, value71, value73, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (264 : Vertex) (408 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 46 = false ∨ valuation q 77 = false ∨ valuation q 90 = false := by
  rw [value46, value71, value77, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (264 : Vertex) (424 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 73 = false ∨ valuation q 77 = false ∨ valuation q 90 = false := by
  rw [value71, value73, value77, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (408 : Vertex) (424 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 173 = true ∨ valuation q 74 = true := by
  rw [value73, value74, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (408 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(410 : Vertex)] := by decide
  have hg := other_cover q (408 : Vertex) (392 : Vertex) [(410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 173 = true ∨ valuation q 71 = true := by
  rw [value71, value73, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (408 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(392 : Vertex)] := by decide
  have hg := other_cover q (408 : Vertex) (410 : Vertex) [(392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 174 = true ∨ valuation q 75 = true := by
  rw [value74, value75, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(411 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (408 : Vertex) [(411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 54 = false ∨ valuation q 74 = false ∨ valuation q 82 = false := by
  rw [value54, value74, value75, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (283 : Vertex) (410 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 54 = false ∨ valuation q 74 = false ∨ valuation q 98 = false := by
  rw [value54, value74, value75, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (283 : Vertex) (410 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 54 = false ∨ valuation q 82 = false ∨ valuation q 98 = false := by
  rw [value54, value75, value82, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (283 : Vertex) (443 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 82 = false ∨ valuation q 98 = false := by
  rw [value74, value75, value82, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (410 : Vertex) (443 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 9 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value9, value76, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (424 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 176 = true ∨ valuation q 9 = true ∨ valuation q 77 = true := by
  rw [value9, value76, value77, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(160 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (432 : Vertex) [(160 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 177 = true ∨ valuation q 12 = true ∨ valuation q 76 = true := by
  rw [value12, value76, value77, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(168 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (392 : Vertex) [(168 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 178 = true ∨ valuation q 84 = true := by
  rw [value78, value84, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(446 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (174 : Vertex) [(446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 178 = true ∨ valuation q 16 = true := by
  rw [value16, value78, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(174 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (446 : Vertex) [(174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 179 = true ∨ valuation q 80 = true ∨ valuation q 81 = true := by
  rw [value79, value80, value81, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(434 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (416 : Vertex) [(434 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 179 = true ∨ valuation q 76 = true ∨ valuation q 80 = true := by
  rw [value76, value79, value80, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(416 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (436 : Vertex) [(416 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 180 = true := by
  rw [value80, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (434 : Vertex) (432 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E147.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112147
