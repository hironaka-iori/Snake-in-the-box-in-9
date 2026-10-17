import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 154 = true ∨ valuation q 36 = true ∨ valuation q 94 = true := by
  rw [value36, value38, value94, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(168 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (174 : Vertex) [(168 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 154 = true ∨ valuation q 36 = true ∨ valuation q 39 = true := by
  rw [value36, value38, value39, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(168 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (428 : Vertex) [(168 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value34, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (166 : Vertex) (170 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 40 = false := by
  rw [value34, value37, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (166 : Vertex) (170 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 34 = false ∨ valuation q 38 = false ∨ valuation q 40 = false := by
  rw [value34, value38, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (166 : Vertex) (172 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 40 = false := by
  rw [value37, value38, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (170 : Vertex) (172 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 39 = true ∨ valuation q 96 = true := by
  rw [value39, value40, value96, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (167 : Vertex) → w ∈ [(174 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (167 : Vertex) [(174 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 35 = true ∨ valuation q 96 = true := by
  rw [value35, value40, value96, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(167 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (174 : Vertex) [(167 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 35 = true ∨ valuation q 39 = true := by
  rw [value35, value39, value40, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(167 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (431 : Vertex) [(167 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 158 = true ∨ valuation q 44 = true ∨ valuation q 100 = true := by
  rw [value42, value44, value100, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(182 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (180 : Vertex) (181 : Vertex) [(182 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 158 = true ∨ valuation q 43 = true ∨ valuation q 100 = true := by
  rw [value42, value43, value100, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(181 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (180 : Vertex) (182 : Vertex) [(181 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 158 = true ∨ valuation q 43 = true ∨ valuation q 44 = true := by
  rw [value42, value43, value44, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(181 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (180 : Vertex) (436 : Vertex) [(181 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 48 = false := by
  rw [value41, value42, value43, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (181 : Vertex) (177 : Vertex) (180 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 160 = true ∨ valuation q 42 = true ∨ valuation q 101 = true := by
  rw [value42, value44, value101, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(180 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (166 : Vertex) [(180 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 41 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value41, value45, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (177 : Vertex) (187 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 37 = false ∨ valuation q 47 = false := by
  rw [value37, value47, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (186 : Vertex) (170 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 47 = true := by
  rw [value46, value47, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(187 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (170 : Vertex) [(187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 37 = true := by
  rw [value37, value46, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(170 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (187 : Vertex) [(170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 163 = true ∨ valuation q 46 = true := by
  rw [value46, value47, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(186 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (185 : Vertex) [(186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 163 = true ∨ valuation q 45 = true := by
  rw [value45, value47, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(185 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (186 : Vertex) [(185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 43 = true ∨ valuation q 104 = true := by
  rw [value43, value48, value104, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(181 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (185 : Vertex) [(181 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 165 = true ∨ valuation q 50 = true ∨ valuation q 53 = true ∨ valuation q 66 = true := by
  rw [value49, value50, value53, value66, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(289 : Vertex), (296 : Vertex), (352 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (416 : Vertex) [(289 : Vertex), (296 : Vertex), (352 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 49 = false ∨ valuation q 58 = false ∨ valuation q 85 = false := by
  rw [value49, value50, value58, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (288 : Vertex) (305 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 167 = true ∨ valuation q 56 = true ∨ valuation q 61 = true ∨ valuation q 89 = true := by
  rw [value51, value56, value61, value89, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (295 : Vertex) → w ∈ [(302 : Vertex), (310 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (295 : Vertex) [(302 : Vertex), (310 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 167 = true ∨ valuation q 52 = true ∨ valuation q 56 = true ∨ valuation q 89 = true := by
  rw [value51, value52, value56, value89, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(295 : Vertex), (302 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (310 : Vertex) [(295 : Vertex), (302 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 167 = true ∨ valuation q 52 = true ∨ valuation q 56 = true ∨ valuation q 61 = true := by
  rw [value51, value52, value56, value61, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(295 : Vertex), (302 : Vertex), (310 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (422 : Vertex) [(295 : Vertex), (302 : Vertex), (310 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 52 = true := by
  rw [value52, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (295 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 168 = true ∨ valuation q 57 = true ∨ valuation q 70 = true ∨ valuation q 90 = true := by
  rw [value52, value57, value70, value90, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(303 : Vertex), (359 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (294 : Vertex) [(303 : Vertex), (359 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 168 = true ∨ valuation q 51 = true ∨ valuation q 57 = true ∨ valuation q 70 = true := by
  rw [value51, value52, value57, value70, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(294 : Vertex), (303 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (423 : Vertex) [(294 : Vertex), (303 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 49 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value49, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (298 : Vertex) (300 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 169 = true ∨ valuation q 49 = true ∨ valuation q 54 = true ∨ valuation q 91 = true := by
  rw [value49, value53, value54, value91, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(288 : Vertex), (298 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (300 : Vertex) [(288 : Vertex), (298 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 63 = false := by
  rw [value53, value54, value56, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (296 : Vertex) (302 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E051.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112051
