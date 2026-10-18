import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 52 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value45, value52, value68, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (264 : Vertex) (320 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 58 = false ∨ valuation q 61 = false := by
  rw [value46, value49, value58, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (261 : Vertex) (273 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 58 = false ∨ valuation q 69 = false ∨ valuation q 77 = false := by
  rw [value46, value58, value69, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (273 : Vertex) (321 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 58 = false ∨ valuation q 87 = false ∨ valuation q 96 = false := by
  rw [value46, value58, value87, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (273 : Vertex) (385 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value47, value50, value53, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (262 : Vertex) (266 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value48, value49, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (276 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value48, value50, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (262 : Vertex) (268 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value50, value51, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (262 : Vertex) (263 : Vertex) (270 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value50, value51, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (262 : Vertex) (263 : Vertex) (326 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 57 = false ∨ valuation q 62 = false ∨ valuation q 67 = false := by
  rw [value51, value57, value62, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (263 : Vertex) (271 : Vertex) (279 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value52, value53, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (264 : Vertex) (266 : Vertex) (268 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value53, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (266 : Vertex) (267 : Vertex) (270 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value54, value57, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (267 : Vertex) (271 : Vertex) (283 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 74 = false ∨ valuation q 76 = false := by
  rw [value54, value57, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (267 : Vertex) (271 : Vertex) (331 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value58, value59, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (273 : Vertex) (275 : Vertex) (277 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value58, value59, value64, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (273 : Vertex) (275 : Vertex) (281 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value58, value59, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (273 : Vertex) (275 : Vertex) (337 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value58, value59, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (273 : Vertex) (275 : Vertex) (401 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value59, value62, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (275 : Vertex) (279 : Vertex) (283 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value63, value64, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (280 : Vertex) (281 : Vertex) (282 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value68, value69, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (321 : Vertex) (328 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value73, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (329 : Vertex) (331 : Vertex) (333 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value91, value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (395 : Vertex) (397 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value95, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (400 : Vertex) (401 : Vertex) (402 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E203.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h⟩

end
end Snake9.Regrowth.E112203
