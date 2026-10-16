import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := by
  have hs : count379 q = (countLit q [190, 191]) + (countLit q [192, 193]) := List.countP_append (p := literal (baseVal q)) (l₁ := [190, 191]) (l₂ := [192, 193])
  have hm := merge_right (literal (valuation q) (377)) (literal (valuation q) (379)) (countLit q [190, 191]) (countLit q [192, 193]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuation q 377 = false ∨ valuation q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 380 = true := by
  have hs : count379 q = (countLit q [190, 191]) + (countLit q [192, 193]) := List.countP_append (p := literal (baseVal q)) (l₁ := [190, 191]) (l₂ := [192, 193])
  have hm := merge_right (literal (valuation q) (378)) (literal (valuation q) (380)) (countLit q [190, 191]) (countLit q [192, 193]) (count379 q) 2 (meaning378 q) (meaning380 q) hs
  change valuation q 378 = false ∨ valuation q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 383 = true := by
  have hs : count383 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal (baseVal q)) (l₁ := [196]) (l₂ := [197])
  have hm := merge_right (literal (valuation q) (197)) (literal (valuation q) (383)) (countLit q [196]) (countLit q [197]) (count383 q) 1 (meaning197 q) (meaning383 q) hs
  change valuation q 197 = false ∨ valuation q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 383 = true := by
  have hs : count383 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal (baseVal q)) (l₁ := [196]) (l₂ := [197])
  have hm := merge_left (literal (valuation q) (196)) (literal (valuation q) (383)) (countLit q [196]) (countLit q [197]) (count383 q) 1 (meaning196 q) (meaning383 q) hs
  change valuation q 196 = false ∨ valuation q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := by
  have hs : count385 q = (countLit q [194, 195]) + (countLit q [196, 197]) := List.countP_append (p := literal (baseVal q)) (l₁ := [194, 195]) (l₂ := [196, 197])
  have hm := merge_right (literal (valuation q) (383)) (literal (valuation q) (385)) (countLit q [194, 195]) (countLit q [196, 197]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuation q 383 = false ∨ valuation q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := by
  have hs : count387 q = (countLit q [190, 191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal (baseVal q)) (l₁ := [190, 191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_right (literal (valuation q) (385)) (literal (valuation q) (387)) (countLit q [190, 191, 192, 193]) (countLit q [194, 195, 196, 197]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuation q 385 = false ∨ valuation q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 387 = true := by
  have hs : count387 q = (countLit q [190, 191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal (baseVal q)) (l₁ := [190, 191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_left (literal (valuation q) (379)) (literal (valuation q) (387)) (countLit q [190, 191, 192, 193]) (countLit q [194, 195, 196, 197]) (count387 q) 1 (meaning379 q) (meaning387 q) hs
  change valuation q 379 = false ∨ valuation q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 385 = false ∨ valuation q 388 = true := by
  have hs : count387 q = (countLit q [190, 191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal (baseVal q)) (l₁ := [190, 191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_two (literal (valuation q) (379)) (literal (valuation q) (385)) (literal (valuation q) (388)) (countLit q [190, 191, 192, 193]) (countLit q [194, 195, 196, 197]) (count387 q) 1 1 (meaning379 q) (meaning385 q) (meaning388 q) hs
  change valuation q 379 = false ∨ valuation q 385 = false ∨ valuation q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 388 = true := by
  have hs : count387 q = (countLit q [190, 191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal (baseVal q)) (l₁ := [190, 191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_left (literal (valuation q) (380)) (literal (valuation q) (388)) (countLit q [190, 191, 192, 193]) (countLit q [194, 195, 196, 197]) (count387 q) 2 (meaning380 q) (meaning388 q) hs
  change valuation q 380 = false ∨ valuation q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = true := by
  have hs : count389 q = (countLit q [183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197])
  have hm := merge_right (literal (valuation q) (387)) (literal (valuation q) (389)) (countLit q [183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) (count389 q) 1 (meaning387 q) (meaning389 q) hs
  change valuation q 387 = false ∨ valuation q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 390 = true := by
  have hs : count389 q = (countLit q [183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197])
  have hm := merge_right (literal (valuation q) (388)) (literal (valuation q) (390)) (countLit q [183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) (count389 q) 2 (meaning388 q) (meaning390 q) hs
  change valuation q 388 = false ∨ valuation q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 389 = true := by
  have hs : count389 q = (countLit q [183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197])
  have hm := merge_left (literal (valuation q) (373)) (literal (valuation q) (389)) (countLit q [183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) (count389 q) 1 (meaning373 q) (meaning389 q) hs
  change valuation q 373 = false ∨ valuation q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 387 = false ∨ valuation q 390 = true := by
  have hs : count389 q = (countLit q [183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197])
  have hm := merge_two (literal (valuation q) (373)) (literal (valuation q) (387)) (literal (valuation q) (390)) (countLit q [183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) (count389 q) 1 1 (meaning373 q) (meaning387 q) (meaning390 q) hs
  change valuation q 373 = false ∨ valuation q 387 = false ∨ valuation q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 391 = true := by
  have hs : count391 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal (baseVal q)) (l₁ := [200]) (l₂ := [201])
  have hm := merge_left (literal (valuation q) (200)) (literal (valuation q) (391)) (countLit q [200]) (countLit q [201]) (count391 q) 1 (meaning200 q) (meaning391 q) hs
  change valuation q 200 = false ∨ valuation q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := by
  have hs : count393 q = (countLit q [199]) + (countLit q [200, 201]) := List.countP_append (p := literal (baseVal q)) (l₁ := [199]) (l₂ := [200, 201])
  have hm := merge_right (literal (valuation q) (391)) (literal (valuation q) (393)) (countLit q [199]) (countLit q [200, 201]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuation q 391 = false ∨ valuation q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 395 = true := by
  have hs : count395 q = (countLit q [202]) + (countLit q [203]) := List.countP_append (p := literal (baseVal q)) (l₁ := [202]) (l₂ := [203])
  have hm := merge_right (literal (valuation q) (203)) (literal (valuation q) (395)) (countLit q [202]) (countLit q [203]) (count395 q) 1 (meaning203 q) (meaning395 q) hs
  change valuation q 203 = false ∨ valuation q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 397 = true := by
  have hs : count397 q = (countLit q [204]) + (countLit q [205]) := List.countP_append (p := literal (baseVal q)) (l₁ := [204]) (l₂ := [205])
  have hm := merge_right (literal (valuation q) (205)) (literal (valuation q) (397)) (countLit q [204]) (countLit q [205]) (count397 q) 1 (meaning205 q) (meaning397 q) hs
  change valuation q 205 = false ∨ valuation q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 397 = true := by
  have hs : count397 q = (countLit q [204]) + (countLit q [205]) := List.countP_append (p := literal (baseVal q)) (l₁ := [204]) (l₂ := [205])
  have hm := merge_left (literal (valuation q) (204)) (literal (valuation q) (397)) (countLit q [204]) (countLit q [205]) (count397 q) 1 (meaning204 q) (meaning397 q) hs
  change valuation q 204 = false ∨ valuation q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := by
  have hs : count399 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal (baseVal q)) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_right (literal (valuation q) (397)) (literal (valuation q) (399)) (countLit q [202, 203]) (countLit q [204, 205]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuation q 397 = false ∨ valuation q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 399 = true := by
  have hs : count399 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal (baseVal q)) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_left (literal (valuation q) (395)) (literal (valuation q) (399)) (countLit q [202, 203]) (countLit q [204, 205]) (count399 q) 1 (meaning395 q) (meaning399 q) hs
  change valuation q 395 = false ∨ valuation q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := by
  have hs : count401 q = (countLit q [199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal (baseVal q)) (l₁ := [199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_right (literal (valuation q) (399)) (literal (valuation q) (401)) (countLit q [199, 200, 201]) (countLit q [202, 203, 204, 205]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuation q 399 = false ∨ valuation q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 401 = true := by
  have hs : count401 q = (countLit q [199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal (baseVal q)) (l₁ := [199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_left (literal (valuation q) (393)) (literal (valuation q) (401)) (countLit q [199, 200, 201]) (countLit q [202, 203, 204, 205]) (count401 q) 1 (meaning393 q) (meaning401 q) hs
  change valuation q 393 = false ∨ valuation q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 399 = false ∨ valuation q 402 = true := by
  have hs : count401 q = (countLit q [199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal (baseVal q)) (l₁ := [199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_two (literal (valuation q) (393)) (literal (valuation q) (399)) (literal (valuation q) (402)) (countLit q [199, 200, 201]) (countLit q [202, 203, 204, 205]) (count401 q) 1 1 (meaning393 q) (meaning399 q) (meaning402 q) hs
  change valuation q 393 = false ∨ valuation q 399 = false ∨ valuation q 402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 405 = true := by
  have hs : count405 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal (baseVal q)) (l₁ := [208]) (l₂ := [209])
  have hm := merge_left (literal (valuation q) (208)) (literal (valuation q) (405)) (countLit q [208]) (countLit q [209]) (count405 q) 1 (meaning208 q) (meaning405 q) hs
  change valuation q 208 = false ∨ valuation q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := by
  have hs : count407 q = (countLit q [206, 207]) + (countLit q [208, 209]) := List.countP_append (p := literal (baseVal q)) (l₁ := [206, 207]) (l₂ := [208, 209])
  have hm := merge_right (literal (valuation q) (405)) (literal (valuation q) (407)) (countLit q [206, 207]) (countLit q [208, 209]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuation q 405 = false ∨ valuation q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 409 = true := by
  have hs : count409 q = (countLit q [210]) + (countLit q [211]) := List.countP_append (p := literal (baseVal q)) (l₁ := [210]) (l₂ := [211])
  have hm := merge_right (literal (valuation q) (211)) (literal (valuation q) (409)) (countLit q [210]) (countLit q [211]) (count409 q) 1 (meaning211 q) (meaning409 q) hs
  change valuation q 211 = false ∨ valuation q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 411 = true := by
  have hs : count411 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [212]) (l₂ := [213])
  have hm := merge_right (literal (valuation q) (213)) (literal (valuation q) (411)) (countLit q [212]) (countLit q [213]) (count411 q) 1 (meaning213 q) (meaning411 q) hs
  change valuation q 213 = false ∨ valuation q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 413 = true := by
  have hs : count413 q = (countLit q [210, 211]) + (countLit q [212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [210, 211]) (l₂ := [212, 213])
  have hm := merge_right (literal (valuation q) (411)) (literal (valuation q) (413)) (countLit q [210, 211]) (countLit q [212, 213]) (count413 q) 1 (meaning411 q) (meaning413 q) hs
  change valuation q 411 = false ∨ valuation q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 413 = true := by
  have hs : count413 q = (countLit q [210, 211]) + (countLit q [212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [210, 211]) (l₂ := [212, 213])
  have hm := merge_left (literal (valuation q) (409)) (literal (valuation q) (413)) (countLit q [210, 211]) (countLit q [212, 213]) (count413 q) 1 (meaning409 q) (meaning413 q) hs
  change valuation q 409 = false ∨ valuation q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := by
  have hs : count415 q = (countLit q [206, 207, 208, 209]) + (countLit q [210, 211, 212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [206, 207, 208, 209]) (l₂ := [210, 211, 212, 213])
  have hm := merge_right (literal (valuation q) (413)) (literal (valuation q) (415)) (countLit q [206, 207, 208, 209]) (countLit q [210, 211, 212, 213]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuation q 413 = false ∨ valuation q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 415 = true := by
  have hs : count415 q = (countLit q [206, 207, 208, 209]) + (countLit q [210, 211, 212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [206, 207, 208, 209]) (l₂ := [210, 211, 212, 213])
  have hm := merge_left (literal (valuation q) (407)) (literal (valuation q) (415)) (countLit q [206, 207, 208, 209]) (countLit q [210, 211, 212, 213]) (count415 q) 1 (meaning407 q) (meaning415 q) hs
  change valuation q 407 = false ∨ valuation q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := by
  have hs : count417 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212, 213])
  have hm := merge_right (literal (valuation q) (415)) (literal (valuation q) (417)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212, 213]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuation q 415 = false ∨ valuation q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block26 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.First112
