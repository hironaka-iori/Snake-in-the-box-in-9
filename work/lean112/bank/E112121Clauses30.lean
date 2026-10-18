import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [142, 143, 144, 145]) + (countLit q [146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [142, 143, 144, 145]) (l₂ := [146, 147, 148, 149])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (293)) (countLit q [142, 143, 144, 145]) (countLit q [146, 147, 148, 149]) (count293 q) 1 (meaning285 q) (meaning293 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 293 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 286 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [142, 143, 144, 145]) + (countLit q [146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [142, 143, 144, 145]) (l₂ := [146, 147, 148, 149])
  have hm := merge_left (literal (valuationOf q) (286)) (literal (valuationOf q) (294)) (countLit q [142, 143, 144, 145]) (countLit q [146, 147, 148, 149]) (count293 q) 2 (meaning286 q) (meaning294 q) hs
  change valuationOf q 286 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 286 = false ∨ valuation q 294 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [152]) + (countLit q [153]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153])
  have hm := merge_left (literal (valuationOf q) (152)) (literal (valuationOf q) (297)) (countLit q [152]) (countLit q [153]) (count297 q) 1 (meaning152 q) (meaning297 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 297 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [150, 151]) + (countLit q [152, 153]) := List.countP_append (p := literal q) (l₁ := [150, 151]) (l₂ := [152, 153])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [150, 151]) (countLit q [152, 153]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [154]) + (countLit q [155]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155])
  have hm := merge_right (literal (valuationOf q) (155)) (literal (valuationOf q) (301)) (countLit q [154]) (countLit q [155]) (count301 q) 1 (meaning155 q) (meaning301 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 301 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [154, 155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [154, 155]) (l₂ := [156, 157])
  have hm := merge_left (literal (valuationOf q) (301)) (literal (valuationOf q) (305)) (countLit q [154, 155]) (countLit q [156, 157]) (count305 q) 1 (meaning301 q) (meaning305 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 305 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [150, 151, 152, 153]) + (countLit q [154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153]) (l₂ := [154, 155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [150, 151, 152, 153]) (countLit q [154, 155, 156, 157]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [150, 151, 152, 153]) + (countLit q [154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153]) (l₂ := [154, 155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (299)) (literal (valuationOf q) (307)) (countLit q [150, 151, 152, 153]) (countLit q [154, 155, 156, 157]) (count307 q) 1 (meaning299 q) (meaning307 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 307 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (309)) (countLit q [142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157]) (count309 q) 1 (meaning293 q) (meaning309 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 309 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (294)) (literal (valuationOf q) (310)) (countLit q [142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157]) (count309 q) 2 (meaning294 q) (meaning310 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 310 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 310 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (310)) (literal (valuationOf q) (312)) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (count311 q) 2 (meaning310 q) (meaning312 q) hs
  change valuationOf q 310 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 310 = false ∨ valuation q 312 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (311)) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (count311 q) 1 (meaning279 q) (meaning311 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 311 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_two (literal (valuationOf q) (279)) (literal (valuationOf q) (309)) (literal (valuationOf q) (312)) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (count311 q) 1 1 (meaning279 q) (meaning309 q) (meaning312 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 309 = false ∨ valuation q 312 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 280 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (280)) (literal (valuationOf q) (312)) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (count311 q) 2 (meaning280 q) (meaning312 q) hs
  change valuationOf q 280 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 280 = false ∨ valuation q 312 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_left (literal (valuationOf q) (159)) (literal (valuationOf q) (313)) (countLit q [159]) (countLit q [160]) (count313 q) 1 (meaning159 q) (meaning313 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 313 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [158]) + (countLit q [159, 160]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159, 160])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [158]) (countLit q [159, 160]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_left (literal (valuationOf q) (163)) (literal (valuationOf q) (319)) (countLit q [163]) (countLit q [164]) (count319 q) 1 (meaning163 q) (meaning319 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 319 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [161, 162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [161, 162]) (l₂ := [163, 164])
  have hm := merge_right (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (countLit q [161, 162]) (countLit q [163, 164]) (count321 q) 1 (meaning319 q) (meaning321 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [158, 159, 160]) + (countLit q [161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160]) (l₂ := [161, 162, 163, 164])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [158, 159, 160]) (countLit q [161, 162, 163, 164]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [158, 159, 160]) + (countLit q [161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160]) (l₂ := [161, 162, 163, 164])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (323)) (countLit q [158, 159, 160]) (countLit q [161, 162, 163, 164]) (count323 q) 1 (meaning315 q) (meaning323 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 323 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_right (literal (valuationOf q) (166)) (literal (valuationOf q) (325)) (countLit q [165]) (countLit q [166]) (count325 q) 1 (meaning166 q) (meaning325 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 325 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_left (literal (valuationOf q) (165)) (literal (valuationOf q) (325)) (countLit q [165]) (countLit q [166]) (count325 q) 1 (meaning165 q) (meaning325 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 325 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_left (literal (valuationOf q) (167)) (literal (valuationOf q) (327)) (countLit q [167]) (countLit q [168]) (count327 q) 1 (meaning167 q) (meaning327 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 327 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [165, 166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [165, 166]) (l₂ := [167, 168])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [165, 166]) (countLit q [167, 168]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [165, 166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [165, 166]) (l₂ := [167, 168])
  have hm := merge_left (literal (valuationOf q) (325)) (literal (valuationOf q) (329)) (countLit q [165, 166]) (countLit q [167, 168]) (count329 q) 1 (meaning325 q) (meaning329 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 329 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [165, 166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [165, 166]) (l₂ := [167, 168])
  have hm := merge_two (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (literal (valuationOf q) (330)) (countLit q [165, 166]) (countLit q [167, 168]) (count329 q) 1 1 (meaning325 q) (meaning327 q) (meaning330 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = false ∨ valuation q 330 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [165, 166, 167, 168]) + (countLit q [169, 170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168]) (l₂ := [169, 170, 171, 172])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (337)) (countLit q [165, 166, 167, 168]) (countLit q [169, 170, 171, 172]) (count337 q) 1 (meaning329 q) (meaning337 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 337 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 330 = false ∨ valuationOf q 338 = true := by
  have hs : count337 q = (countLit q [165, 166, 167, 168]) + (countLit q [169, 170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168]) (l₂ := [169, 170, 171, 172])
  have hm := merge_left (literal (valuationOf q) (330)) (literal (valuationOf q) (338)) (countLit q [165, 166, 167, 168]) (countLit q [169, 170, 171, 172]) (count337 q) 2 (meaning330 q) (meaning338 q) hs
  change valuationOf q 330 = false ∨ valuationOf q 338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 330 = false ∨ valuation q 338 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 338 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172])
  have hm := merge_right (literal (valuationOf q) (338)) (literal (valuationOf q) (340)) (countLit q [158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172]) (count339 q) 2 (meaning338 q) (meaning340 q) hs
  change valuationOf q 338 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 338 = false ∨ valuation q 340 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E121.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112121
