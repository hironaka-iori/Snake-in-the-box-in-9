import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 301 = true := by
  have hs : count301 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_left (literal (valuation q) (271)) (literal (valuation q) (301)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count301 q) 1 (meaning271 q) (meaning301 q) hs
  change valuation q 271 = false ∨ valuation q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 299 = false ∨ valuation q 302 = true := by
  have hs : count301 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_two (literal (valuation q) (271)) (literal (valuation q) (299)) (literal (valuation q) (302)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count301 q) 1 1 (meaning271 q) (meaning299 q) (meaning302 q) hs
  change valuation q 271 = false ∨ valuation q 299 = false ∨ valuation q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 302 = true := by
  have hs : count301 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_left (literal (valuation q) (272)) (literal (valuation q) (302)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count301 q) 2 (meaning272 q) (meaning302 q) hs
  change valuation q 272 = false ∨ valuation q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 303 = true := by
  have hs : count303 q = (countLit q [154]) + (countLit q [155]) := List.countP_append (p := literal (baseVal q)) (l₁ := [154]) (l₂ := [155])
  have hm := merge_left (literal (valuation q) (154)) (literal (valuation q) (303)) (countLit q [154]) (countLit q [155]) (count303 q) 1 (meaning154 q) (meaning303 q) hs
  change valuation q 154 = false ∨ valuation q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := by
  have hs : count305 q = (countLit q [153]) + (countLit q [154, 155]) := List.countP_append (p := literal (baseVal q)) (l₁ := [153]) (l₂ := [154, 155])
  have hm := merge_right (literal (valuation q) (303)) (literal (valuation q) (305)) (countLit q [153]) (countLit q [154, 155]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuation q 303 = false ∨ valuation q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 309 = true := by
  have hs : count309 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal (baseVal q)) (l₁ := [158]) (l₂ := [159])
  have hm := merge_right (literal (valuation q) (159)) (literal (valuation q) (309)) (countLit q [158]) (countLit q [159]) (count309 q) 1 (meaning159 q) (meaning309 q) hs
  change valuation q 159 = false ∨ valuation q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 309 = true := by
  have hs : count309 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal (baseVal q)) (l₁ := [158]) (l₂ := [159])
  have hm := merge_left (literal (valuation q) (158)) (literal (valuation q) (309)) (countLit q [158]) (countLit q [159]) (count309 q) 1 (meaning158 q) (meaning309 q) hs
  change valuation q 158 = false ∨ valuation q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := by
  have hs : count311 q = (countLit q [156, 157]) + (countLit q [158, 159]) := List.countP_append (p := literal (baseVal q)) (l₁ := [156, 157]) (l₂ := [158, 159])
  have hm := merge_right (literal (valuation q) (309)) (literal (valuation q) (311)) (countLit q [156, 157]) (countLit q [158, 159]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuation q 309 = false ∨ valuation q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := by
  have hs : count313 q = (countLit q [153, 154, 155]) + (countLit q [156, 157, 158, 159]) := List.countP_append (p := literal (baseVal q)) (l₁ := [153, 154, 155]) (l₂ := [156, 157, 158, 159])
  have hm := merge_right (literal (valuation q) (311)) (literal (valuation q) (313)) (countLit q [153, 154, 155]) (countLit q [156, 157, 158, 159]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuation q 311 = false ∨ valuation q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 313 = true := by
  have hs : count313 q = (countLit q [153, 154, 155]) + (countLit q [156, 157, 158, 159]) := List.countP_append (p := literal (baseVal q)) (l₁ := [153, 154, 155]) (l₂ := [156, 157, 158, 159])
  have hm := merge_left (literal (valuation q) (305)) (literal (valuation q) (313)) (countLit q [153, 154, 155]) (countLit q [156, 157, 158, 159]) (count313 q) 1 (meaning305 q) (meaning313 q) hs
  change valuation q 305 = false ∨ valuation q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 315 = true := by
  have hs : count315 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal (baseVal q)) (l₁ := [160]) (l₂ := [161])
  have hm := merge_left (literal (valuation q) (160)) (literal (valuation q) (315)) (countLit q [160]) (countLit q [161]) (count315 q) 1 (meaning160 q) (meaning315 q) hs
  change valuation q 160 = false ∨ valuation q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 317 = true := by
  have hs : count317 q = (countLit q [162]) + (countLit q [163]) := List.countP_append (p := literal (baseVal q)) (l₁ := [162]) (l₂ := [163])
  have hm := merge_left (literal (valuation q) (162)) (literal (valuation q) (317)) (countLit q [162]) (countLit q [163]) (count317 q) 1 (meaning162 q) (meaning317 q) hs
  change valuation q 162 = false ∨ valuation q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := by
  have hs : count319 q = (countLit q [160, 161]) + (countLit q [162, 163]) := List.countP_append (p := literal (baseVal q)) (l₁ := [160, 161]) (l₂ := [162, 163])
  have hm := merge_right (literal (valuation q) (317)) (literal (valuation q) (319)) (countLit q [160, 161]) (countLit q [162, 163]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuation q 317 = false ∨ valuation q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 319 = true := by
  have hs : count319 q = (countLit q [160, 161]) + (countLit q [162, 163]) := List.countP_append (p := literal (baseVal q)) (l₁ := [160, 161]) (l₂ := [162, 163])
  have hm := merge_left (literal (valuation q) (315)) (literal (valuation q) (319)) (countLit q [160, 161]) (countLit q [162, 163]) (count319 q) 1 (meaning315 q) (meaning319 q) hs
  change valuation q 315 = false ∨ valuation q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 323 = true := by
  have hs : count323 q = (countLit q [166]) + (countLit q [167]) := List.countP_append (p := literal (baseVal q)) (l₁ := [166]) (l₂ := [167])
  have hm := merge_left (literal (valuation q) (166)) (literal (valuation q) (323)) (countLit q [166]) (countLit q [167]) (count323 q) 1 (meaning166 q) (meaning323 q) hs
  change valuation q 166 = false ∨ valuation q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 325 = true := by
  have hs : count325 q = (countLit q [164, 165]) + (countLit q [166, 167]) := List.countP_append (p := literal (baseVal q)) (l₁ := [164, 165]) (l₂ := [166, 167])
  have hm := merge_right (literal (valuation q) (323)) (literal (valuation q) (325)) (countLit q [164, 165]) (countLit q [166, 167]) (count325 q) 1 (meaning323 q) (meaning325 q) hs
  change valuation q 323 = false ∨ valuation q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := by
  have hs : count327 q = (countLit q [160, 161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal (baseVal q)) (l₁ := [160, 161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_right (literal (valuation q) (325)) (literal (valuation q) (327)) (countLit q [160, 161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuation q 325 = false ∨ valuation q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 327 = true := by
  have hs : count327 q = (countLit q [160, 161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal (baseVal q)) (l₁ := [160, 161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_left (literal (valuation q) (319)) (literal (valuation q) (327)) (countLit q [160, 161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 1 (meaning319 q) (meaning327 q) hs
  change valuation q 319 = false ∨ valuation q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := by
  have hs : count329 q = (countLit q [153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) := List.countP_append (p := literal (baseVal q)) (l₁ := [153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167])
  have hm := merge_right (literal (valuation q) (327)) (literal (valuation q) (329)) (countLit q [153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuation q 327 = false ∨ valuation q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 329 = true := by
  have hs : count329 q = (countLit q [153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) := List.countP_append (p := literal (baseVal q)) (l₁ := [153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167])
  have hm := merge_left (literal (valuation q) (313)) (literal (valuation q) (329)) (countLit q [153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) (count329 q) 1 (meaning313 q) (meaning329 q) hs
  change valuation q 313 = false ∨ valuation q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 331 = true := by
  have hs : count331 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal (baseVal q)) (l₁ := [169]) (l₂ := [170])
  have hm := merge_right (literal (valuation q) (170)) (literal (valuation q) (331)) (countLit q [169]) (countLit q [170]) (count331 q) 1 (meaning170 q) (meaning331 q) hs
  change valuation q 170 = false ∨ valuation q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := by
  have hs : count333 q = (countLit q [168]) + (countLit q [169, 170]) := List.countP_append (p := literal (baseVal q)) (l₁ := [168]) (l₂ := [169, 170])
  have hm := merge_right (literal (valuation q) (331)) (literal (valuation q) (333)) (countLit q [168]) (countLit q [169, 170]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuation q 331 = false ∨ valuation q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 333 = true := by
  have hs : count333 q = (countLit q [168]) + (countLit q [169, 170]) := List.countP_append (p := literal (baseVal q)) (l₁ := [168]) (l₂ := [169, 170])
  have hm := merge_left (literal (valuation q) (168)) (literal (valuation q) (333)) (countLit q [168]) (countLit q [169, 170]) (count333 q) 1 (meaning168 q) (meaning333 q) hs
  change valuation q 168 = false ∨ valuation q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 337 = true := by
  have hs : count337 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal (baseVal q)) (l₁ := [173]) (l₂ := [174])
  have hm := merge_right (literal (valuation q) (174)) (literal (valuation q) (337)) (countLit q [173]) (countLit q [174]) (count337 q) 1 (meaning174 q) (meaning337 q) hs
  change valuation q 174 = false ∨ valuation q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 337 = true := by
  have hs : count337 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal (baseVal q)) (l₁ := [173]) (l₂ := [174])
  have hm := merge_left (literal (valuation q) (173)) (literal (valuation q) (337)) (countLit q [173]) (countLit q [174]) (count337 q) 1 (meaning173 q) (meaning337 q) hs
  change valuation q 173 = false ∨ valuation q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 174 = false ∨ valuation q 338 = true := by
  have hs : count337 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal (baseVal q)) (l₁ := [173]) (l₂ := [174])
  have hm := merge_two (literal (valuation q) (173)) (literal (valuation q) (174)) (literal (valuation q) (338)) (countLit q [173]) (countLit q [174]) (count337 q) 1 1 (meaning173 q) (meaning174 q) (meaning338 q) hs
  change valuation q 173 = false ∨ valuation q 174 = false ∨ valuation q 338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := by
  have hs : count339 q = (countLit q [171, 172]) + (countLit q [173, 174]) := List.countP_append (p := literal (baseVal q)) (l₁ := [171, 172]) (l₂ := [173, 174])
  have hm := merge_right (literal (valuation q) (337)) (literal (valuation q) (339)) (countLit q [171, 172]) (countLit q [173, 174]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuation q 337 = false ∨ valuation q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 338 = false ∨ valuation q 340 = true := by
  have hs : count339 q = (countLit q [171, 172]) + (countLit q [173, 174]) := List.countP_append (p := literal (baseVal q)) (l₁ := [171, 172]) (l₂ := [173, 174])
  have hm := merge_right (literal (valuation q) (338)) (literal (valuation q) (340)) (countLit q [171, 172]) (countLit q [173, 174]) (count339 q) 2 (meaning338 q) (meaning340 q) hs
  change valuation q 338 = false ∨ valuation q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := by
  have hs : count341 q = (countLit q [168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal (baseVal q)) (l₁ := [168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_right (literal (valuation q) (339)) (literal (valuation q) (341)) (countLit q [168, 169, 170]) (countLit q [171, 172, 173, 174]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuation q 339 = false ∨ valuation q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 340 = false ∨ valuation q 342 = true := by
  have hs : count341 q = (countLit q [168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal (baseVal q)) (l₁ := [168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_right (literal (valuation q) (340)) (literal (valuation q) (342)) (countLit q [168, 169, 170]) (countLit q [171, 172, 173, 174]) (count341 q) 2 (meaning340 q) (meaning342 q) hs
  change valuation q 340 = false ∨ valuation q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 341 = true := by
  have hs : count341 q = (countLit q [168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal (baseVal q)) (l₁ := [168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_left (literal (valuation q) (333)) (literal (valuation q) (341)) (countLit q [168, 169, 170]) (countLit q [171, 172, 173, 174]) (count341 q) 1 (meaning333 q) (meaning341 q) hs
  change valuation q 333 = false ∨ valuation q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 343 = true := by
  have hs : count343 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal (baseVal q)) (l₁ := [175]) (l₂ := [176])
  have hm := merge_right (literal (valuation q) (176)) (literal (valuation q) (343)) (countLit q [175]) (countLit q [176]) (count343 q) 1 (meaning176 q) (meaning343 q) hs
  change valuation q 176 = false ∨ valuation q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block24 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.First112
