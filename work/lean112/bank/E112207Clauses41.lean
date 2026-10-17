import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false := by
  rw [value1690]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1673 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 45 = false ∨ valuation q 46 = false := by
  rw [value1, value2, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (256 : Vertex) (257 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 15 = false ∨ valuation q 20 = false := by
  rw [value1, value4, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (8 : Vertex) (128 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 45 = false ∨ valuation q 52 = false := by
  rw [value1, value4, value45, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (8 : Vertex) (256 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 15 = false ∨ valuation q 45 = false ∨ valuation q 85 = false := by
  rw [value1, value15, value45, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (128 : Vertex) (256 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 46 = false ∨ valuation q 58 = false := by
  rw [value2, value8, value46, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (1 : Vertex) (17 : Vertex) (257 : Vertex) (273 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 20 = false ∨ valuation q 52 = false ∨ valuation q 90 = false := by
  rw [value4, value20, value52, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (8 : Vertex) (136 : Vertex) (264 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value5, value7, value54, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (11 : Vertex) (15 : Vertex) (267 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 20 = false ∨ valuation q 85 = false ∨ valuation q 90 = false := by
  rw [value15, value20, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (128 : Vertex) (136 : Vertex) (384 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value17, value18, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (134 : Vertex) (140 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value20, value21, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (136 : Vertex) (137 : Vertex) (392 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 31 = false ∨ valuation q 32 = false := by
  rw [value26, value27, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (149 : Vertex) (151 : Vertex) (157 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 52 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value45, value52, value68, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (264 : Vertex) (320 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 52 = false ∨ valuation q 85 = false ∨ valuation q 90 = false := by
  rw [value45, value52, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (264 : Vertex) (384 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value48, value49, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (276 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value48, value50, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (262 : Vertex) (268 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value49, value51, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (263 : Vertex) (277 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value50, value51, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (262 : Vertex) (263 : Vertex) (326 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value52, value53, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (264 : Vertex) (266 : Vertex) (268 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value52, value53, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (264 : Vertex) (266 : Vertex) (280 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value53, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (266 : Vertex) (267 : Vertex) (270 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value54, value57, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (267 : Vertex) (271 : Vertex) (283 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 74 = false ∨ valuation q 76 = false := by
  rw [value54, value57, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (267 : Vertex) (271 : Vertex) (331 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 92 = false ∨ valuation q 94 = false := by
  rw [value54, value57, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (267 : Vertex) (271 : Vertex) (395 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value58, value59, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (273 : Vertex) (275 : Vertex) (277 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value58, value59, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (273 : Vertex) (275 : Vertex) (401 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value63, value64, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (280 : Vertex) (281 : Vertex) (282 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value68, value69, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (321 : Vertex) (328 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value73, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (329 : Vertex) (331 : Vertex) (333 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 84 = false := by
  rw [value78, value80, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (338 : Vertex) (342 : Vertex) (346 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value85, value86, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (385 : Vertex) (392 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value85, value86, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (385 : Vertex) (400 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E207.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112207
