import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [221, 222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [221, 222]) (l₂ := [223, 224])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [221, 222]) (countLit q [223, 224]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [221, 222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [221, 222]) (l₂ := [223, 224])
  have hm := merge_left (literal (valuationOf q) (433)) (literal (valuationOf q) (437)) (countLit q [221, 222]) (countLit q [223, 224]) (count437 q) 1 (meaning433 q) (meaning437 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 437 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_right (literal (valuationOf q) (226)) (literal (valuationOf q) (439)) (countLit q [225]) (countLit q [226]) (count439 q) 1 (meaning226 q) (meaning439 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 439 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_left (literal (valuationOf q) (225)) (literal (valuationOf q) (439)) (countLit q [225]) (countLit q [226]) (count439 q) 1 (meaning225 q) (meaning439 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 439 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [227]) + (countLit q [228]) := List.countP_append (p := literal q) (l₁ := [227]) (l₂ := [228])
  have hm := merge_right (literal (valuationOf q) (228)) (literal (valuationOf q) (441)) (countLit q [227]) (countLit q [228]) (count441 q) 1 (meaning228 q) (meaning441 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 441 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_right (literal (valuationOf q) (441)) (literal (valuationOf q) (443)) (countLit q [225, 226]) (countLit q [227, 228]) (count443 q) 1 (meaning441 q) (meaning443 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 443 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_left (literal (valuationOf q) (439)) (literal (valuationOf q) (443)) (countLit q [225, 226]) (countLit q [227, 228]) (count443 q) 1 (meaning439 q) (meaning443 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 443 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 441 = false ∨ valuationOf q 444 = true := by
  have hs : count443 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_two (literal (valuationOf q) (439)) (literal (valuationOf q) (441)) (literal (valuationOf q) (444)) (countLit q [225, 226]) (countLit q [227, 228]) (count443 q) 1 1 (meaning439 q) (meaning441 q) (meaning444 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 441 = false ∨ valuationOf q 444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 441 = false ∨ valuation q 444 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [221, 222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [221, 222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (countLit q [221, 222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 444 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [221, 222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [221, 222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (444)) (literal (valuationOf q) (446)) (countLit q [221, 222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 2 (meaning444 q) (meaning446 q) hs
  change valuationOf q 444 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 444 = false ∨ valuation q 446 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [221, 222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [221, 222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (445)) (countLit q [221, 222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 (meaning437 q) (meaning445 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 445 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 443 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [221, 222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [221, 222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_two (literal (valuationOf q) (437)) (literal (valuationOf q) (443)) (literal (valuationOf q) (446)) (countLit q [221, 222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 1 (meaning437 q) (meaning443 q) (meaning446 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 443 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 443 = false ∨ valuation q 446 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [214, 215, 216, 217, 218, 219, 220]) + (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220]) (l₂ := [221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (445)) (literal (valuationOf q) (447)) (countLit q [214, 215, 216, 217, 218, 219, 220]) (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 1 (meaning445 q) (meaning447 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 447 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 446 = false ∨ valuationOf q 448 = true := by
  have hs : count447 q = (countLit q [214, 215, 216, 217, 218, 219, 220]) + (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220]) (l₂ := [221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (446)) (literal (valuationOf q) (448)) (countLit q [214, 215, 216, 217, 218, 219, 220]) (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 2 (meaning446 q) (meaning448 q) hs
  change valuationOf q 446 = false ∨ valuationOf q 448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 446 = false ∨ valuation q 448 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [214, 215, 216, 217, 218, 219, 220]) + (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220]) (l₂ := [221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (431)) (literal (valuationOf q) (447)) (countLit q [214, 215, 216, 217, 218, 219, 220]) (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 1 (meaning431 q) (meaning447 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 447 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 445 = false ∨ valuationOf q 448 = true := by
  have hs : count447 q = (countLit q [214, 215, 216, 217, 218, 219, 220]) + (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220]) (l₂ := [221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_two (literal (valuationOf q) (431)) (literal (valuationOf q) (445)) (literal (valuationOf q) (448)) (countLit q [214, 215, 216, 217, 218, 219, 220]) (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 1 1 (meaning431 q) (meaning445 q) (meaning448 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 445 = false ∨ valuationOf q 448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 445 = false ∨ valuation q 448 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 232 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_right (literal (valuationOf q) (232)) (literal (valuationOf q) (451)) (countLit q [231]) (countLit q [232]) (count451 q) 1 (meaning232 q) (meaning451 q) hs
  change valuationOf q 232 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 451 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (451)) (countLit q [231]) (countLit q [232]) (count451 q) 1 (meaning231 q) (meaning451 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 451 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_right (literal (valuationOf q) (451)) (literal (valuationOf q) (453)) (countLit q [229, 230]) (countLit q [231, 232]) (count453 q) 1 (meaning451 q) (meaning453 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 453 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 236 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [235]) + (countLit q [236]) := List.countP_append (p := literal q) (l₁ := [235]) (l₂ := [236])
  have hm := merge_right (literal (valuationOf q) (236)) (literal (valuationOf q) (457)) (countLit q [235]) (countLit q [236]) (count457 q) 1 (meaning236 q) (meaning457 q) hs
  change valuationOf q 236 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 457 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_right (literal (valuationOf q) (457)) (literal (valuationOf q) (459)) (countLit q [233, 234]) (countLit q [235, 236]) (count459 q) 1 (meaning457 q) (meaning459 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 459 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (459)) (literal (valuationOf q) (461)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count461 q) 1 (meaning459 q) (meaning461 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (453)) (literal (valuationOf q) (461)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count461 q) 1 (meaning453 q) (meaning461 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 461 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [237]) + (countLit q [238]) := List.countP_append (p := literal q) (l₁ := [237]) (l₂ := [238])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (463)) (countLit q [237]) (countLit q [238]) (count463 q) 1 (meaning237 q) (meaning463 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 463 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [239]) + (countLit q [240]) := List.countP_append (p := literal q) (l₁ := [239]) (l₂ := [240])
  have hm := merge_right (literal (valuationOf q) (240)) (literal (valuationOf q) (465)) (countLit q [239]) (countLit q [240]) (count465 q) 1 (meaning240 q) (meaning465 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 465 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [239]) + (countLit q [240]) := List.countP_append (p := literal q) (l₁ := [239]) (l₂ := [240])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (465)) (countLit q [239]) (countLit q [240]) (count465 q) 1 (meaning239 q) (meaning465 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 465 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 240 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [239]) + (countLit q [240]) := List.countP_append (p := literal q) (l₁ := [239]) (l₂ := [240])
  have hm := merge_two (literal (valuationOf q) (239)) (literal (valuationOf q) (240)) (literal (valuationOf q) (466)) (countLit q [239]) (countLit q [240]) (count465 q) 1 1 (meaning239 q) (meaning240 q) (meaning466 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 240 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 240 = false ∨ valuation q 466 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 466 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_right (literal (valuationOf q) (466)) (literal (valuationOf q) (468)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 2 (meaning466 q) (meaning468 q) hs
  change valuationOf q 466 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 466 = false ∨ valuation q 468 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_left (literal (valuationOf q) (463)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning463 q) (meaning467 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 467 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [243]) + (countLit q [244]) := List.countP_append (p := literal q) (l₁ := [243]) (l₂ := [244])
  have hm := merge_right (literal (valuationOf q) (244)) (literal (valuationOf q) (471)) (countLit q [243]) (countLit q [244]) (count471 q) 1 (meaning244 q) (meaning471 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 471 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [243]) + (countLit q [244]) := List.countP_append (p := literal q) (l₁ := [243]) (l₂ := [244])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (471)) (countLit q [243]) (countLit q [244]) (count471 q) 1 (meaning243 q) (meaning471 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 471 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E258.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112258
