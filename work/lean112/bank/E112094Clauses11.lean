import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 896 = true := by
  have hs : count892 q = (countLit q [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75]) + (countLit q [-79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75]) (l₂ := [-79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102])
  have hm := merge_right (literal (valuationOf q) (885)) (literal (valuationOf q) (896)) (countLit q [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75]) (countLit q [-79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]) (count892 q) 5 (meaning885 q) (meaning896 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 896 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 897 = true := by
  have hs : count892 q = (countLit q [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75]) + (countLit q [-79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75]) (l₂ := [-79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102])
  have hm := merge_right (literal (valuationOf q) (886)) (literal (valuationOf q) (897)) (countLit q [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75]) (countLit q [-79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]) (count892 q) 6 (meaning886 q) (meaning897 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 897 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 898 = true := by
  have hs : count892 q = (countLit q [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75]) + (countLit q [-79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75]) (l₂ := [-79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102])
  have hm := merge_right (literal (valuationOf q) (887)) (literal (valuationOf q) (898)) (countLit q [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75]) (countLit q [-79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]) (count892 q) 7 (meaning887 q) (meaning898 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 898 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 898 = false ∨ valuationOf q 913 = true := by
  have hs : count903 q = (countLit q [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) + (countLit q [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75, -79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) (l₂ := [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75, -79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (898)) (literal (valuationOf q) (913)) (countLit q [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) (countLit q [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75, -79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]) (count903 q) 4 7 (meaning790 q) (meaning898 q) (meaning913 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 898 = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 898 = false ∨ valuation q 913 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 791 = false ∨ valuationOf q 897 = false ∨ valuationOf q 913 = true := by
  have hs : count903 q = (countLit q [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) + (countLit q [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75, -79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) (l₂ := [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75, -79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (791)) (literal (valuationOf q) (897)) (literal (valuationOf q) (913)) (countLit q [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) (countLit q [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75, -79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]) (count903 q) 5 6 (meaning791 q) (meaning897 q) (meaning913 q) hs
  change valuationOf q 791 = false ∨ valuationOf q 897 = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 791 = false ∨ valuation q 897 = false ∨ valuation q 913 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 896 = false ∨ valuationOf q 913 = true := by
  have hs : count903 q = (countLit q [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) + (countLit q [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75, -79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) (l₂ := [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75, -79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (792)) (literal (valuationOf q) (896)) (literal (valuationOf q) (913)) (countLit q [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) (countLit q [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75, -79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]) (count903 q) 6 5 (meaning792 q) (meaning896 q) (meaning913 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 896 = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 896 = false ∨ valuation q 913 = true := counterClause358 (baseVal q)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 913 = false := by
  rw [value913]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count903 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause360 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1210 = true := by
  have hs : count1210 q = (countLit q [-5]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (1210)) (countLit q [-5]) (countLit q [-6]) (count1210 q) 1 (meaningNeg6 q) (meaning1210 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1210 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1210 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1210 = true := by
  have hs : count1210 q = (countLit q [-5]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-6])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (1210)) (countLit q [-5]) (countLit q [-6]) (count1210 q) 1 (meaningNeg5 q) (meaning1210 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1210 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1210 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 6 = true ∨ valuationOf q 1211 = true := by
  have hs : count1210 q = (countLit q [-5]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-6])
  have hm := merge_two (literal (valuationOf q) (-5)) (literal (valuationOf q) (-6)) (literal (valuationOf q) (1211)) (countLit q [-5]) (countLit q [-6]) (count1210 q) 1 1 (meaningNeg5 q) (meaningNeg6 q) (meaning1211 q) hs
  change (! (valuationOf q 5)) = false ∨ (! (valuationOf q 6)) = false ∨ valuationOf q 1211 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 6 = true ∨ valuation q 1211 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 1210 = false ∨ valuationOf q 1212 = true := by
  have hs : count1212 q = (countLit q [-3]) + (countLit q [-5, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -6])
  have hm := merge_right (literal (valuationOf q) (1210)) (literal (valuationOf q) (1212)) (countLit q [-3]) (countLit q [-5, -6]) (count1212 q) 1 (meaning1210 q) (meaning1212 q) hs
  change valuationOf q 1210 = false ∨ valuationOf q 1212 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 1210 = false ∨ valuation q 1212 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 1211 = false ∨ valuationOf q 1213 = true := by
  have hs : count1212 q = (countLit q [-3]) + (countLit q [-5, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -6])
  have hm := merge_right (literal (valuationOf q) (1211)) (literal (valuationOf q) (1213)) (countLit q [-3]) (countLit q [-5, -6]) (count1212 q) 2 (meaning1211 q) (meaning1213 q) hs
  change valuationOf q 1211 = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 1211 = false ∨ valuation q 1213 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1212 = true := by
  have hs : count1212 q = (countLit q [-3]) + (countLit q [-5, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -6])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1212)) (countLit q [-3]) (countLit q [-5, -6]) (count1212 q) 1 (meaningNeg3 q) (meaning1212 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1212 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1212 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1210 = false ∨ valuationOf q 1213 = true := by
  have hs : count1212 q = (countLit q [-3]) + (countLit q [-5, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5, -6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1210)) (literal (valuationOf q) (1213)) (countLit q [-3]) (countLit q [-5, -6]) (count1212 q) 1 1 (meaningNeg3 q) (meaning1210 q) (meaning1213 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1210 = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1210 = false ∨ valuation q 1213 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1215 = true := by
  have hs : count1215 q = (countLit q [-9]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1215)) (countLit q [-9]) (countLit q [-12]) (count1215 q) 1 (meaningNeg12 q) (meaning1215 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1215 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1215 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 1215 = false ∨ valuationOf q 1217 = true := by
  have hs : count1217 q = (countLit q [-8]) + (countLit q [-9, -12]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -12])
  have hm := merge_right (literal (valuationOf q) (1215)) (literal (valuationOf q) (1217)) (countLit q [-8]) (countLit q [-9, -12]) (count1217 q) 1 (meaning1215 q) (meaning1217 q) hs
  change valuationOf q 1215 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 1215 = false ∨ valuation q 1217 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1217 = true := by
  have hs : count1217 q = (countLit q [-8]) + (countLit q [-9, -12]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -12])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1217)) (countLit q [-8]) (countLit q [-9, -12]) (count1217 q) 1 (meaningNeg8 q) (meaning1217 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1217 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1215 = false ∨ valuationOf q 1218 = true := by
  have hs : count1217 q = (countLit q [-8]) + (countLit q [-9, -12]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -12])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1215)) (literal (valuationOf q) (1218)) (countLit q [-8]) (countLit q [-9, -12]) (count1217 q) 1 1 (meaningNeg8 q) (meaning1215 q) (meaning1218 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1215 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1215 = false ∨ valuation q 1218 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 1217 = false ∨ valuationOf q 1220 = true := by
  have hs : count1220 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -9, -12])
  have hm := merge_right (literal (valuationOf q) (1217)) (literal (valuationOf q) (1220)) (countLit q [-3, -5, -6]) (countLit q [-8, -9, -12]) (count1220 q) 1 (meaning1217 q) (meaning1220 q) hs
  change valuationOf q 1217 = false ∨ valuationOf q 1220 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 1217 = false ∨ valuation q 1220 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 1218 = false ∨ valuationOf q 1221 = true := by
  have hs : count1220 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -9, -12])
  have hm := merge_right (literal (valuationOf q) (1218)) (literal (valuationOf q) (1221)) (countLit q [-3, -5, -6]) (countLit q [-8, -9, -12]) (count1220 q) 2 (meaning1218 q) (meaning1221 q) hs
  change valuationOf q 1218 = false ∨ valuationOf q 1221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 1218 = false ∨ valuation q 1221 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1220 = true := by
  have hs : count1220 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -9, -12])
  have hm := merge_left (literal (valuationOf q) (1212)) (literal (valuationOf q) (1220)) (countLit q [-3, -5, -6]) (countLit q [-8, -9, -12]) (count1220 q) 1 (meaning1212 q) (meaning1220 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1220 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1220 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1221 = true := by
  have hs : count1220 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -9, -12])
  have hm := merge_two (literal (valuationOf q) (1212)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1221)) (countLit q [-3, -5, -6]) (countLit q [-8, -9, -12]) (count1220 q) 1 1 (meaning1212 q) (meaning1217 q) (meaning1221 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1217 = false ∨ valuation q 1221 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1222 = true := by
  have hs : count1220 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -9, -12])
  have hm := merge_two (literal (valuationOf q) (1212)) (literal (valuationOf q) (1218)) (literal (valuationOf q) (1222)) (countLit q [-3, -5, -6]) (countLit q [-8, -9, -12]) (count1220 q) 1 2 (meaning1212 q) (meaning1218 q) (meaning1222 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1222 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1218 = false ∨ valuation q 1222 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 1213 = false ∨ valuationOf q 1221 = true := by
  have hs : count1220 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -9, -12])
  have hm := merge_left (literal (valuationOf q) (1213)) (literal (valuationOf q) (1221)) (countLit q [-3, -5, -6]) (countLit q [-8, -9, -12]) (count1220 q) 2 (meaning1213 q) (meaning1221 q) hs
  change valuationOf q 1213 = false ∨ valuationOf q 1221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 1213 = false ∨ valuation q 1221 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 1213 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1222 = true := by
  have hs : count1220 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -9, -12])
  have hm := merge_two (literal (valuationOf q) (1213)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1222)) (countLit q [-3, -5, -6]) (countLit q [-8, -9, -12]) (count1220 q) 2 1 (meaning1213 q) (meaning1217 q) (meaning1222 q) hs
  change valuationOf q 1213 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1222 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 1213 = false ∨ valuation q 1217 = false ∨ valuation q 1222 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1226 = true := by
  have hs : count1226 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1226)) (countLit q [-15]) (countLit q [-17]) (count1226 q) 1 (meaningNeg17 q) (meaning1226 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1226 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1226 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1226 = true := by
  have hs : count1226 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1226)) (countLit q [-15]) (countLit q [-17]) (count1226 q) 1 (meaningNeg15 q) (meaning1226 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1226 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1226 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 17 = true ∨ valuationOf q 1227 = true := by
  have hs : count1226 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (1227)) (countLit q [-15]) (countLit q [-17]) (count1226 q) 1 1 (meaningNeg15 q) (meaningNeg17 q) (meaning1227 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 1227 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 1227 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 1226 = false ∨ valuationOf q 1228 = true := by
  have hs : count1228 q = (countLit q [-13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -17])
  have hm := merge_right (literal (valuationOf q) (1226)) (literal (valuationOf q) (1228)) (countLit q [-13]) (countLit q [-15, -17]) (count1228 q) 1 (meaning1226 q) (meaning1228 q) hs
  change valuationOf q 1226 = false ∨ valuationOf q 1228 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 1226 = false ∨ valuation q 1228 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 1227 = false ∨ valuationOf q 1229 = true := by
  have hs : count1228 q = (countLit q [-13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -17])
  have hm := merge_right (literal (valuationOf q) (1227)) (literal (valuationOf q) (1229)) (countLit q [-13]) (countLit q [-15, -17]) (count1228 q) 2 (meaning1227 q) (meaning1229 q) hs
  change valuationOf q 1227 = false ∨ valuationOf q 1229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 1227 = false ∨ valuation q 1229 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1231 = true := by
  have hs : count1231 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1231)) (countLit q [-20]) (countLit q [-22]) (count1231 q) 1 (meaningNeg22 q) (meaning1231 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1231 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1231 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1231 = true := by
  have hs : count1231 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1231)) (countLit q [-20]) (countLit q [-22]) (count1231 q) 1 (meaningNeg20 q) (meaning1231 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1231 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1231 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E094.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112094
