import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false := by
  rw [value1052]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1036 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 8 = false := by
  rw [value3, value4, value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (6 : Vertex) (7 : Vertex) (14 : Vertex) (15 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 16 = false := by
  rw [value9, value11, value13, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (17 : Vertex) (21 : Vertex) (25 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value34, value35, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (166 : Vertex) (167 : Vertex) (174 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 40 = false ∨ valuation q 90 = false ∨ valuation q 96 = false := by
  rw [value35, value40, value90, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (167 : Vertex) (175 : Vertex) (423 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value36, value38, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (168 : Vertex) (172 : Vertex) (424 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 44 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value42, value44, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (180 : Vertex) (182 : Vertex) (436 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value51, value52, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (294 : Vertex) (295 : Vertex) (302 : Vertex) (303 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value51, value52, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (294 : Vertex) (295 : Vertex) (422 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value53, value55, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (296 : Vertex) (300 : Vertex) (424 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 61 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value59, value61, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (308 : Vertex) (310 : Vertex) (436 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value67, value68, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (353 : Vertex) (355 : Vertex) (361 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value85, value87, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (417 : Vertex) (419 : Vertex) (425 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value86, value87, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (418 : Vertex) (419 : Vertex) (434 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value86, value89, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (418 : Vertex) (422 : Vertex) (482 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 96 = false := by
  rw [value87, value90, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (419 : Vertex) (423 : Vertex) (427 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value91, value94, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (428 : Vertex) (488 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 100 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value97, value100, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (432 : Vertex) (436 : Vertex) (440 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E051.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h⟩

end
end Snake9.Regrowth.E112051
