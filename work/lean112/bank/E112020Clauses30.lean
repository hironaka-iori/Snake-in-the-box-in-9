import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [219]) + (countLit q [220]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220])
  have hm := merge_left (literal (valuationOf q) (219)) (literal (valuationOf q) (429)) (countLit q [219]) (countLit q [220]) (count429 q) 1 (meaning219 q) (meaning429 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 429 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219, 220])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [218]) (countLit q [219, 220]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [221]) + (countLit q [222]) := List.countP_append (p := literal q) (l₁ := [221]) (l₂ := [222])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (433)) (countLit q [221]) (countLit q [222]) (count433 q) 1 (meaning221 q) (meaning433 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 433 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [221, 222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [221, 222]) (l₂ := [223, 224])
  have hm := merge_left (literal (valuationOf q) (433)) (literal (valuationOf q) (437)) (countLit q [221, 222]) (countLit q [223, 224]) (count437 q) 1 (meaning433 q) (meaning437 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 437 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [218, 219, 220]) + (countLit q [221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220]) (l₂ := [221, 222, 223, 224])
  have hm := merge_right (literal (valuationOf q) (437)) (literal (valuationOf q) (439)) (countLit q [218, 219, 220]) (countLit q [221, 222, 223, 224]) (count439 q) 1 (meaning437 q) (meaning439 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 439 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [218, 219, 220]) + (countLit q [221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220]) (l₂ := [221, 222, 223, 224])
  have hm := merge_left (literal (valuationOf q) (431)) (literal (valuationOf q) (439)) (countLit q [218, 219, 220]) (countLit q [221, 222, 223, 224]) (count439 q) 1 (meaning431 q) (meaning439 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 439 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_right (literal (valuationOf q) (226)) (literal (valuationOf q) (441)) (countLit q [225]) (countLit q [226]) (count441 q) 1 (meaning226 q) (meaning441 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 441 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_left (literal (valuationOf q) (225)) (literal (valuationOf q) (441)) (countLit q [225]) (countLit q [226]) (count441 q) 1 (meaning225 q) (meaning441 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 441 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 226 = false ∨ valuationOf q 442 = true := by
  have hs : count441 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_two (literal (valuationOf q) (225)) (literal (valuationOf q) (226)) (literal (valuationOf q) (442)) (countLit q [225]) (countLit q [226]) (count441 q) 1 1 (meaning225 q) (meaning226 q) (meaning442 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 226 = false ∨ valuationOf q 442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 226 = false ∨ valuation q 442 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_left (literal (valuationOf q) (441)) (literal (valuationOf q) (445)) (countLit q [225, 226]) (countLit q [227, 228]) (count445 q) 1 (meaning441 q) (meaning445 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 445 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 442 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_left (literal (valuationOf q) (442)) (literal (valuationOf q) (446)) (countLit q [225, 226]) (countLit q [227, 228]) (count445 q) 2 (meaning442 q) (meaning446 q) hs
  change valuationOf q 442 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 442 = false ∨ valuation q 446 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal q) (l₁ := [229]) (l₂ := [230])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (447)) (countLit q [229]) (countLit q [230]) (count447 q) 1 (meaning229 q) (meaning447 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 447 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_left (literal (valuationOf q) (447)) (literal (valuationOf q) (451)) (countLit q [229, 230]) (countLit q [231, 232]) (count451 q) 1 (meaning447 q) (meaning451 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 451 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [225, 226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (451)) (literal (valuationOf q) (453)) (countLit q [225, 226, 227, 228]) (countLit q [229, 230, 231, 232]) (count453 q) 1 (meaning451 q) (meaning453 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 453 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [225, 226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (445)) (literal (valuationOf q) (453)) (countLit q [225, 226, 227, 228]) (countLit q [229, 230, 231, 232]) (count453 q) 1 (meaning445 q) (meaning453 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 453 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 446 = false ∨ valuationOf q 454 = true := by
  have hs : count453 q = (countLit q [225, 226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (446)) (literal (valuationOf q) (454)) (countLit q [225, 226, 227, 228]) (countLit q [229, 230, 231, 232]) (count453 q) 2 (meaning446 q) (meaning454 q) hs
  change valuationOf q 446 = false ∨ valuationOf q 454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 446 = false ∨ valuation q 454 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 454 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (454)) (literal (valuationOf q) (456)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 2 (meaning454 q) (meaning456 q) hs
  change valuationOf q 454 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 454 = false ∨ valuation q 456 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (439)) (literal (valuationOf q) (455)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 (meaning439 q) (meaning455 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 455 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (439)) (literal (valuationOf q) (453)) (literal (valuationOf q) (456)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 1 (meaning439 q) (meaning453 q) (meaning456 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 453 = false ∨ valuation q 456 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_right (literal (valuationOf q) (234)) (literal (valuationOf q) (457)) (countLit q [233]) (countLit q [234]) (count457 q) 1 (meaning234 q) (meaning457 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 457 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 236 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [235]) + (countLit q [236]) := List.countP_append (p := literal q) (l₁ := [235]) (l₂ := [236])
  have hm := merge_right (literal (valuationOf q) (236)) (literal (valuationOf q) (459)) (countLit q [235]) (countLit q [236]) (count459 q) 1 (meaning236 q) (meaning459 q) hs
  change valuationOf q 236 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 459 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_right (literal (valuationOf q) (459)) (literal (valuationOf q) (461)) (countLit q [233, 234]) (countLit q [235, 236]) (count461 q) 1 (meaning459 q) (meaning461 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_left (literal (valuationOf q) (457)) (literal (valuationOf q) (461)) (countLit q [233, 234]) (countLit q [235, 236]) (count461 q) 1 (meaning457 q) (meaning461 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 461 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [237]) + (countLit q [238]) := List.countP_append (p := literal q) (l₁ := [237]) (l₂ := [238])
  have hm := merge_right (literal (valuationOf q) (238)) (literal (valuationOf q) (463)) (countLit q [237]) (countLit q [238]) (count463 q) 1 (meaning238 q) (meaning463 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 463 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [239]) + (countLit q [240]) := List.countP_append (p := literal q) (l₁ := [239]) (l₂ := [240])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (465)) (countLit q [239]) (countLit q [240]) (count465 q) 1 (meaning239 q) (meaning465 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 465 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_left (literal (valuationOf q) (463)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning463 q) (meaning467 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 467 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (467)) (literal (valuationOf q) (469)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 (meaning467 q) (meaning469 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 469 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (461)) (literal (valuationOf q) (469)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 (meaning461 q) (meaning469 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 469 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [243]) + (countLit q [244]) := List.countP_append (p := literal q) (l₁ := [243]) (l₂ := [244])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (473)) (countLit q [243]) (countLit q [244]) (count473 q) 1 (meaning243 q) (meaning473 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 473 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [241, 242]) + (countLit q [243, 244]) := List.countP_append (p := literal q) (l₁ := [241, 242]) (l₂ := [243, 244])
  have hm := merge_right (literal (valuationOf q) (473)) (literal (valuationOf q) (475)) (countLit q [241, 242]) (countLit q [243, 244]) (count475 q) 1 (meaning473 q) (meaning475 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 475 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E020.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112020
