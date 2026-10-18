import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec59 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1889 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value56, value57, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (206 : Vertex) (207 : Vertex) (462 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1890 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value58, value59, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (209 : Vertex) (211 : Vertex) (213 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1891 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value58, value59, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (209 : Vertex) (211 : Vertex) (217 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1892 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value58, value60, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (209 : Vertex) (213 : Vertex) (465 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1893 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value67, value68, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (322 : Vertex) (448 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1894 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value68, value70, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (322 : Vertex) (326 : Vertex) (450 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1895 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value69, value71, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (325 : Vertex) (327 : Vertex) (341 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1896 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value70, value71, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (326 : Vertex) (327 : Vertex) (334 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1897 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 107 = false ∨ valuation q 112 = false := by
  rw [value70, value74, value107, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (326 : Vertex) (334 : Vertex) (454 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1898 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value72, value73, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (328 : Vertex) (329 : Vertex) (344 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1899 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value74, value75, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (334 : Vertex) (335 : Vertex) (462 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1900 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value77, value78, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (340 : Vertex) (341 : Vertex) (468 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1901 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 83 = false ∨ valuation q 117 = false ∨ valuation q 121 = false := by
  rw [value77, value83, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (340 : Vertex) (348 : Vertex) (468 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1902 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value84, value85, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (386 : Vertex) (448 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1903 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value85, value87, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (390 : Vertex) (450 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1904 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value86, value88, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (389 : Vertex) (391 : Vertex) (405 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1905 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 95 = false ∨ valuation q 106 = false ∨ valuation q 118 = false := by
  rw [value86, value95, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (389 : Vertex) (405 : Vertex) (453 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1906 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value87, value88, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (390 : Vertex) (391 : Vertex) (398 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1907 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 107 = false ∨ valuation q 112 = false := by
  rw [value87, value91, value107, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (390 : Vertex) (398 : Vertex) (454 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1908 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value89, value90, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (392 : Vertex) (393 : Vertex) (408 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1909 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value91, value92, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (398 : Vertex) (399 : Vertex) (462 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1910 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 101 = false ∨ valuation q 117 = false ∨ valuation q 121 = false := by
  rw [value94, value101, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (404 : Vertex) (412 : Vertex) (468 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1911 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value97, value98, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (408 : Vertex) (409 : Vertex) (410 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1912 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value102, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (448 : Vertex) (449 : Vertex) (450 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1913 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value102, value103, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (448 : Vertex) (449 : Vertex) (464 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1914 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 104 = false ∨ valuation q 114 = false ∨ valuation q 116 = false := by
  rw [value102, value104, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (448 : Vertex) (450 : Vertex) (464 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1915 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value103, value105, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (451 : Vertex) (457 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1916 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 106 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value103, value106, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (453 : Vertex) (465 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1917 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 107 = false ∨ valuation q 116 = false ∨ valuation q 119 = false := by
  rw [value104, value107, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (450 : Vertex) (454 : Vertex) (466 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1918 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 111 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value106, value111, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (453 : Vertex) (461 : Vertex) (469 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1919 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 112 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value107, value112, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (454 : Vertex) (462 : Vertex) (470 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1920 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value110, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (460 : Vertex) (461 : Vertex) (462 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block59 (q : Snake 81) (h : Conditions q) : B112E105.Block59 (valuation q) :=
  ⟨clause1889 q h, clause1890 q h, clause1891 q h, clause1892 q h, clause1893 q h, clause1894 q h, clause1895 q h, clause1896 q h, clause1897 q h, clause1898 q h, clause1899 q h, clause1900 q h, clause1901 q h, clause1902 q h, clause1903 q h, clause1904 q h, clause1905 q h, clause1906 q h, clause1907 q h, clause1908 q h, clause1909 q h, clause1910 q h, clause1911 q h, clause1912 q h, clause1913 q h, clause1914 q h, clause1915 q h, clause1916 q h, clause1917 q h, clause1918 q h, clause1919 q h, clause1920 q h⟩

end
end Snake9.Regrowth.E112105
