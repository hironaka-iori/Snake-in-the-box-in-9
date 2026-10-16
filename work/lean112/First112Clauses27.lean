import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 417 = true := by
  have hs : count417 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212, 213])
  have hm := merge_left (literal (valuation q) (401)) (literal (valuation q) (417)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212, 213]) (count417 q) 1 (meaning401 q) (meaning417 q) hs
  change valuation q 401 = false ∨ valuation q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 415 = false ∨ valuation q 418 = true := by
  have hs : count417 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212, 213])
  have hm := merge_two (literal (valuation q) (401)) (literal (valuation q) (415)) (literal (valuation q) (418)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212, 213]) (count417 q) 1 1 (meaning401 q) (meaning415 q) (meaning418 q) hs
  change valuation q 401 = false ∨ valuation q 415 = false ∨ valuation q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 402 = false ∨ valuation q 418 = true := by
  have hs : count417 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212, 213])
  have hm := merge_left (literal (valuation q) (402)) (literal (valuation q) (418)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212, 213]) (count417 q) 2 (meaning402 q) (meaning418 q) hs
  change valuation q 402 = false ∨ valuation q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = true := by
  have hs : count419 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213])
  have hm := merge_right (literal (valuation q) (417)) (literal (valuation q) (419)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (count419 q) 1 (meaning417 q) (meaning419 q) hs
  change valuation q 417 = false ∨ valuation q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 420 = true := by
  have hs : count419 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213])
  have hm := merge_right (literal (valuation q) (418)) (literal (valuation q) (420)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (count419 q) 2 (meaning418 q) (meaning420 q) hs
  change valuation q 418 = false ∨ valuation q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 419 = true := by
  have hs : count419 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213])
  have hm := merge_left (literal (valuation q) (389)) (literal (valuation q) (419)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (count419 q) 1 (meaning389 q) (meaning419 q) hs
  change valuation q 389 = false ∨ valuation q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 417 = false ∨ valuation q 420 = true := by
  have hs : count419 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213])
  have hm := merge_two (literal (valuation q) (389)) (literal (valuation q) (417)) (literal (valuation q) (420)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (count419 q) 1 1 (meaning389 q) (meaning417 q) (meaning420 q) hs
  change valuation q 389 = false ∨ valuation q 417 = false ∨ valuation q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 390 = false ∨ valuation q 420 = true := by
  have hs : count419 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213])
  have hm := merge_left (literal (valuation q) (390)) (literal (valuation q) (420)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (count419 q) 2 (meaning390 q) (meaning420 q) hs
  change valuation q 390 = false ∨ valuation q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 421 = true := by
  have hs : count421 q = (countLit q [215]) + (countLit q [216]) := List.countP_append (p := literal (baseVal q)) (l₁ := [215]) (l₂ := [216])
  have hm := merge_right (literal (valuation q) (216)) (literal (valuation q) (421)) (countLit q [215]) (countLit q [216]) (count421 q) 1 (meaning216 q) (meaning421 q) hs
  change valuation q 216 = false ∨ valuation q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := by
  have hs : count423 q = (countLit q [214]) + (countLit q [215, 216]) := List.countP_append (p := literal (baseVal q)) (l₁ := [214]) (l₂ := [215, 216])
  have hm := merge_right (literal (valuation q) (421)) (literal (valuation q) (423)) (countLit q [214]) (countLit q [215, 216]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuation q 421 = false ∨ valuation q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 425 = true := by
  have hs : count425 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal (baseVal q)) (l₁ := [217]) (l₂ := [218])
  have hm := merge_right (literal (valuation q) (218)) (literal (valuation q) (425)) (countLit q [217]) (countLit q [218]) (count425 q) 1 (meaning218 q) (meaning425 q) hs
  change valuation q 218 = false ∨ valuation q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 429 = true := by
  have hs : count429 q = (countLit q [217, 218]) + (countLit q [219, 220]) := List.countP_append (p := literal (baseVal q)) (l₁ := [217, 218]) (l₂ := [219, 220])
  have hm := merge_left (literal (valuation q) (425)) (literal (valuation q) (429)) (countLit q [217, 218]) (countLit q [219, 220]) (count429 q) 1 (meaning425 q) (meaning429 q) hs
  change valuation q 425 = false ∨ valuation q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := by
  have hs : count431 q = (countLit q [214, 215, 216]) + (countLit q [217, 218, 219, 220]) := List.countP_append (p := literal (baseVal q)) (l₁ := [214, 215, 216]) (l₂ := [217, 218, 219, 220])
  have hm := merge_right (literal (valuation q) (429)) (literal (valuation q) (431)) (countLit q [214, 215, 216]) (countLit q [217, 218, 219, 220]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuation q 429 = false ∨ valuation q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 431 = true := by
  have hs : count431 q = (countLit q [214, 215, 216]) + (countLit q [217, 218, 219, 220]) := List.countP_append (p := literal (baseVal q)) (l₁ := [214, 215, 216]) (l₂ := [217, 218, 219, 220])
  have hm := merge_left (literal (valuation q) (423)) (literal (valuation q) (431)) (countLit q [214, 215, 216]) (countLit q [217, 218, 219, 220]) (count431 q) 1 (meaning423 q) (meaning431 q) hs
  change valuation q 423 = false ∨ valuation q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 433 = true := by
  have hs : count433 q = (countLit q [221]) + (countLit q [222]) := List.countP_append (p := literal (baseVal q)) (l₁ := [221]) (l₂ := [222])
  have hm := merge_right (literal (valuation q) (222)) (literal (valuation q) (433)) (countLit q [221]) (countLit q [222]) (count433 q) 1 (meaning222 q) (meaning433 q) hs
  change valuation q 222 = false ∨ valuation q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 433 = true := by
  have hs : count433 q = (countLit q [221]) + (countLit q [222]) := List.countP_append (p := literal (baseVal q)) (l₁ := [221]) (l₂ := [222])
  have hm := merge_left (literal (valuation q) (221)) (literal (valuation q) (433)) (countLit q [221]) (countLit q [222]) (count433 q) 1 (meaning221 q) (meaning433 q) hs
  change valuation q 221 = false ∨ valuation q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 224 = false ∨ valuation q 435 = true := by
  have hs : count435 q = (countLit q [223]) + (countLit q [224]) := List.countP_append (p := literal (baseVal q)) (l₁ := [223]) (l₂ := [224])
  have hm := merge_right (literal (valuation q) (224)) (literal (valuation q) (435)) (countLit q [223]) (countLit q [224]) (count435 q) 1 (meaning224 q) (meaning435 q) hs
  change valuation q 224 = false ∨ valuation q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := by
  have hs : count437 q = (countLit q [221, 222]) + (countLit q [223, 224]) := List.countP_append (p := literal (baseVal q)) (l₁ := [221, 222]) (l₂ := [223, 224])
  have hm := merge_right (literal (valuation q) (435)) (literal (valuation q) (437)) (countLit q [221, 222]) (countLit q [223, 224]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuation q 435 = false ∨ valuation q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 437 = true := by
  have hs : count437 q = (countLit q [221, 222]) + (countLit q [223, 224]) := List.countP_append (p := literal (baseVal q)) (l₁ := [221, 222]) (l₂ := [223, 224])
  have hm := merge_left (literal (valuation q) (433)) (literal (valuation q) (437)) (countLit q [221, 222]) (countLit q [223, 224]) (count437 q) 1 (meaning433 q) (meaning437 q) hs
  change valuation q 433 = false ∨ valuation q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 439 = true := by
  have hs : count439 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal (baseVal q)) (l₁ := [225]) (l₂ := [226])
  have hm := merge_left (literal (valuation q) (225)) (literal (valuation q) (439)) (countLit q [225]) (countLit q [226]) (count439 q) 1 (meaning225 q) (meaning439 q) hs
  change valuation q 225 = false ∨ valuation q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 441 = true := by
  have hs : count441 q = (countLit q [227]) + (countLit q [228]) := List.countP_append (p := literal (baseVal q)) (l₁ := [227]) (l₂ := [228])
  have hm := merge_right (literal (valuation q) (228)) (literal (valuation q) (441)) (countLit q [227]) (countLit q [228]) (count441 q) 1 (meaning228 q) (meaning441 q) hs
  change valuation q 228 = false ∨ valuation q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 443 = true := by
  have hs : count443 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal (baseVal q)) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_right (literal (valuation q) (441)) (literal (valuation q) (443)) (countLit q [225, 226]) (countLit q [227, 228]) (count443 q) 1 (meaning441 q) (meaning443 q) hs
  change valuation q 441 = false ∨ valuation q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 443 = true := by
  have hs : count443 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal (baseVal q)) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_left (literal (valuation q) (439)) (literal (valuation q) (443)) (countLit q [225, 226]) (countLit q [227, 228]) (count443 q) 1 (meaning439 q) (meaning443 q) hs
  change valuation q 439 = false ∨ valuation q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := by
  have hs : count445 q = (countLit q [221, 222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal (baseVal q)) (l₁ := [221, 222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_right (literal (valuation q) (443)) (literal (valuation q) (445)) (countLit q [221, 222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuation q 443 = false ∨ valuation q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 445 = true := by
  have hs : count445 q = (countLit q [221, 222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal (baseVal q)) (l₁ := [221, 222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_left (literal (valuation q) (437)) (literal (valuation q) (445)) (countLit q [221, 222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 (meaning437 q) (meaning445 q) hs
  change valuation q 437 = false ∨ valuation q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 447 = true := by
  have hs : count447 q = (countLit q [214, 215, 216, 217, 218, 219, 220]) + (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal (baseVal q)) (l₁ := [214, 215, 216, 217, 218, 219, 220]) (l₂ := [221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuation q) (445)) (literal (valuation q) (447)) (countLit q [214, 215, 216, 217, 218, 219, 220]) (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 1 (meaning445 q) (meaning447 q) hs
  change valuation q 445 = false ∨ valuation q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 447 = true := by
  have hs : count447 q = (countLit q [214, 215, 216, 217, 218, 219, 220]) + (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal (baseVal q)) (l₁ := [214, 215, 216, 217, 218, 219, 220]) (l₂ := [221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuation q) (431)) (literal (valuation q) (447)) (countLit q [214, 215, 216, 217, 218, 219, 220]) (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 1 (meaning431 q) (meaning447 q) hs
  change valuation q 431 = false ∨ valuation q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 449 = true := by
  have hs : count449 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal (baseVal q)) (l₁ := [229]) (l₂ := [230])
  have hm := merge_right (literal (valuation q) (230)) (literal (valuation q) (449)) (countLit q [229]) (countLit q [230]) (count449 q) 1 (meaning230 q) (meaning449 q) hs
  change valuation q 230 = false ∨ valuation q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 449 = true := by
  have hs : count449 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal (baseVal q)) (l₁ := [229]) (l₂ := [230])
  have hm := merge_left (literal (valuation q) (229)) (literal (valuation q) (449)) (countLit q [229]) (countLit q [230]) (count449 q) 1 (meaning229 q) (meaning449 q) hs
  change valuation q 229 = false ∨ valuation q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 453 = true := by
  have hs : count453 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal (baseVal q)) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_left (literal (valuation q) (449)) (literal (valuation q) (453)) (countLit q [229, 230]) (countLit q [231, 232]) (count453 q) 1 (meaning449 q) (meaning453 q) hs
  change valuation q 449 = false ∨ valuation q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 455 = true := by
  have hs : count455 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal (baseVal q)) (l₁ := [233]) (l₂ := [234])
  have hm := merge_right (literal (valuation q) (234)) (literal (valuation q) (455)) (countLit q [233]) (countLit q [234]) (count455 q) 1 (meaning234 q) (meaning455 q) hs
  change valuation q 234 = false ∨ valuation q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 457 = true := by
  have hs : count457 q = (countLit q [235]) + (countLit q [236]) := List.countP_append (p := literal (baseVal q)) (l₁ := [235]) (l₂ := [236])
  have hm := merge_right (literal (valuation q) (236)) (literal (valuation q) (457)) (countLit q [235]) (countLit q [236]) (count457 q) 1 (meaning236 q) (meaning457 q) hs
  change valuation q 236 = false ∨ valuation q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block27 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.First112
