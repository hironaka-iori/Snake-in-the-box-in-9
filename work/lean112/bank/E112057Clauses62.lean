import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec62 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1985 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 50 = false ∨ valuation q 52 = false := by
  rw [value40, value42, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (133 : Vertex) (135 : Vertex) (149 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1986 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 47 = false ∨ valuation q 112 = false ∨ valuation q 115 = false := by
  rw [value40, value47, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (133 : Vertex) (141 : Vertex) (389 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1987 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 46 = false := by
  rw [value43, value44, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1988 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value49, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (148 : Vertex) (149 : Vertex) (150 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1989 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value51, value52, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (150 : Vertex) (151 : Vertex) (406 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1990 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 72 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value68, value72, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (259 : Vertex) (263 : Vertex) (267 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1991 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value69, value70, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (262 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1992 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value69, value70, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (268 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1993 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value69, value70, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (276 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1994 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 81 = false ∨ valuation q 83 = false := by
  rw [value69, value71, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (262 : Vertex) (276 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1995 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 76 = false ∨ valuation q 81 = false ∨ valuation q 89 = false := by
  rw [value69, value76, value81, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (268 : Vertex) (276 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1996 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value70, value72, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (263 : Vertex) (269 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1997 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value70, value72, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (263 : Vertex) (277 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1998 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 77 = false ∨ valuation q 95 = false ∨ valuation q 98 = false := by
  rw [value70, value77, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (269 : Vertex) (325 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1999 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value71, value72, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (262 : Vertex) (263 : Vertex) (278 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2000 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value73, value74, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (264 : Vertex) (265 : Vertex) (268 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2001 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value73, value74, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (264 : Vertex) (265 : Vertex) (280 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2002 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 76 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value73, value76, value85, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (264 : Vertex) (268 : Vertex) (280 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2003 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value74, value75, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (265 : Vertex) (267 : Vertex) (269 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2004 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value74, value75, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (265 : Vertex) (267 : Vertex) (281 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2005 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value75, value78, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (267 : Vertex) (271 : Vertex) (283 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2006 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 89 = false ∨ valuation q 114 = false ∨ valuation q 124 = false := by
  rw [value76, value89, value114, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (268 : Vertex) (284 : Vertex) (396 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2007 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 83 = false := by
  rw [value79, value80, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (272 : Vertex) (274 : Vertex) (276 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2008 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value79, value80, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (272 : Vertex) (274 : Vertex) (280 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2009 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value81, value82, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (276 : Vertex) (277 : Vertex) (278 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2010 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value83, value84, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (278 : Vertex) (279 : Vertex) (342 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2011 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 90 = false ∨ valuation q 103 = false ∨ valuation q 108 = false := by
  rw [value84, value90, value103, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (279 : Vertex) (287 : Vertex) (343 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2012 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value85, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (280 : Vertex) (281 : Vertex) (282 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2013 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value86, value88, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (281 : Vertex) (283 : Vertex) (345 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2014 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value86, value88, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (281 : Vertex) (283 : Vertex) (409 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2015 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value88, value90, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (283 : Vertex) (287 : Vertex) (347 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2016 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 123 = false ∨ valuation q 126 = false := by
  rw [value88, value90, value123, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (283 : Vertex) (287 : Vertex) (411 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block62 (q : Snake 81) (h : Conditions q) : B112E057.Block62 (valuation q) :=
  ⟨clause1985 q h, clause1986 q h, clause1987 q h, clause1988 q h, clause1989 q h, clause1990 q h, clause1991 q h, clause1992 q h, clause1993 q h, clause1994 q h, clause1995 q h, clause1996 q h, clause1997 q h, clause1998 q h, clause1999 q h, clause2000 q h, clause2001 q h, clause2002 q h, clause2003 q h, clause2004 q h, clause2005 q h, clause2006 q h, clause2007 q h, clause2008 q h, clause2009 q h, clause2010 q h, clause2011 q h, clause2012 q h, clause2013 q h, clause2014 q h, clause2015 q h, clause2016 q h⟩

end
end Snake9.Regrowth.E112057
