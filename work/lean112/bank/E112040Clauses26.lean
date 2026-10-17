import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 384 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209])
  have hm := merge_left (literal (valuationOf q) (384)) (literal (valuationOf q) (414)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (count413 q) 2 (meaning384 q) (meaning414 q) hs
  change valuationOf q 384 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 384 = false ∨ valuation q 414 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [213]) + (countLit q [214]) := List.countP_append (p := literal q) (l₁ := [213]) (l₂ := [214])
  have hm := merge_left (literal (valuationOf q) (213)) (literal (valuationOf q) (419)) (countLit q [213]) (countLit q [214]) (count419 q) 1 (meaning213 q) (meaning419 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 419 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [213, 214]) + (countLit q [215, 216]) := List.countP_append (p := literal q) (l₁ := [213, 214]) (l₂ := [215, 216])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (423)) (countLit q [213, 214]) (countLit q [215, 216]) (count423 q) 1 (meaning419 q) (meaning423 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 423 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [210, 211, 212]) + (countLit q [213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212]) (l₂ := [213, 214, 215, 216])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [210, 211, 212]) (countLit q [213, 214, 215, 216]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (427)) (countLit q [217]) (countLit q [218]) (count427 q) 1 (meaning217 q) (meaning427 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 427 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [219]) + (countLit q [220]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220])
  have hm := merge_right (literal (valuationOf q) (220)) (literal (valuationOf q) (429)) (countLit q [219]) (countLit q [220]) (count429 q) 1 (meaning220 q) (meaning429 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 429 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [217, 218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [217, 218]) (l₂ := [219, 220])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [217, 218]) (countLit q [219, 220]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [217, 218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [217, 218]) (l₂ := [219, 220])
  have hm := merge_left (literal (valuationOf q) (427)) (literal (valuationOf q) (431)) (countLit q [217, 218]) (countLit q [219, 220]) (count431 q) 1 (meaning427 q) (meaning431 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 431 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [221]) + (countLit q [222]) := List.countP_append (p := literal q) (l₁ := [221]) (l₂ := [222])
  have hm := merge_right (literal (valuationOf q) (222)) (literal (valuationOf q) (433)) (countLit q [221]) (countLit q [222]) (count433 q) 1 (meaning222 q) (meaning433 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 433 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [221]) + (countLit q [222]) := List.countP_append (p := literal q) (l₁ := [221]) (l₂ := [222])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (433)) (countLit q [221]) (countLit q [222]) (count433 q) 1 (meaning221 q) (meaning433 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 433 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 224 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [223]) + (countLit q [224]) := List.countP_append (p := literal q) (l₁ := [223]) (l₂ := [224])
  have hm := merge_right (literal (valuationOf q) (224)) (literal (valuationOf q) (435)) (countLit q [223]) (countLit q [224]) (count435 q) 1 (meaning224 q) (meaning435 q) hs
  change valuationOf q 224 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 224 = false ∨ valuation q 435 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [223]) + (countLit q [224]) := List.countP_append (p := literal q) (l₁ := [223]) (l₂ := [224])
  have hm := merge_left (literal (valuationOf q) (223)) (literal (valuationOf q) (435)) (countLit q [223]) (countLit q [224]) (count435 q) 1 (meaning223 q) (meaning435 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 435 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [221, 222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [221, 222]) (l₂ := [223, 224])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [221, 222]) (countLit q [223, 224]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [221, 222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [221, 222]) (l₂ := [223, 224])
  have hm := merge_left (literal (valuationOf q) (433)) (literal (valuationOf q) (437)) (countLit q [221, 222]) (countLit q [223, 224]) (count437 q) 1 (meaning433 q) (meaning437 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 437 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [217, 218, 219, 220]) + (countLit q [221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [217, 218, 219, 220]) (l₂ := [221, 222, 223, 224])
  have hm := merge_right (literal (valuationOf q) (437)) (literal (valuationOf q) (439)) (countLit q [217, 218, 219, 220]) (countLit q [221, 222, 223, 224]) (count439 q) 1 (meaning437 q) (meaning439 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 439 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [217, 218, 219, 220]) + (countLit q [221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [217, 218, 219, 220]) (l₂ := [221, 222, 223, 224])
  have hm := merge_left (literal (valuationOf q) (431)) (literal (valuationOf q) (439)) (countLit q [217, 218, 219, 220]) (countLit q [221, 222, 223, 224]) (count439 q) 1 (meaning431 q) (meaning439 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 439 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 437 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [217, 218, 219, 220]) + (countLit q [221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [217, 218, 219, 220]) (l₂ := [221, 222, 223, 224])
  have hm := merge_two (literal (valuationOf q) (431)) (literal (valuationOf q) (437)) (literal (valuationOf q) (440)) (countLit q [217, 218, 219, 220]) (countLit q [221, 222, 223, 224]) (count439 q) 1 1 (meaning431 q) (meaning437 q) (meaning440 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 437 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 437 = false ∨ valuation q 440 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [210, 211, 212, 213, 214, 215, 216]) + (countLit q [217, 218, 219, 220, 221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213, 214, 215, 216]) (l₂ := [217, 218, 219, 220, 221, 222, 223, 224])
  have hm := merge_right (literal (valuationOf q) (439)) (literal (valuationOf q) (441)) (countLit q [210, 211, 212, 213, 214, 215, 216]) (countLit q [217, 218, 219, 220, 221, 222, 223, 224]) (count441 q) 1 (meaning439 q) (meaning441 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 441 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 440 = false ∨ valuationOf q 442 = true := by
  have hs : count441 q = (countLit q [210, 211, 212, 213, 214, 215, 216]) + (countLit q [217, 218, 219, 220, 221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213, 214, 215, 216]) (l₂ := [217, 218, 219, 220, 221, 222, 223, 224])
  have hm := merge_right (literal (valuationOf q) (440)) (literal (valuationOf q) (442)) (countLit q [210, 211, 212, 213, 214, 215, 216]) (countLit q [217, 218, 219, 220, 221, 222, 223, 224]) (count441 q) 2 (meaning440 q) (meaning442 q) hs
  change valuationOf q 440 = false ∨ valuationOf q 442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 440 = false ∨ valuation q 442 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [210, 211, 212, 213, 214, 215, 216]) + (countLit q [217, 218, 219, 220, 221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213, 214, 215, 216]) (l₂ := [217, 218, 219, 220, 221, 222, 223, 224])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (441)) (countLit q [210, 211, 212, 213, 214, 215, 216]) (countLit q [217, 218, 219, 220, 221, 222, 223, 224]) (count441 q) 1 (meaning425 q) (meaning441 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 441 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [226]) + (countLit q [227]) := List.countP_append (p := literal q) (l₁ := [226]) (l₂ := [227])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (443)) (countLit q [226]) (countLit q [227]) (count443 q) 1 (meaning227 q) (meaning443 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 443 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [225]) + (countLit q [226, 227]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226, 227])
  have hm := merge_right (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (countLit q [225]) (countLit q [226, 227]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [225, 226, 227]) + (countLit q [228, 229, 230, 231]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227]) (l₂ := [228, 229, 230, 231])
  have hm := merge_left (literal (valuationOf q) (445)) (literal (valuationOf q) (453)) (countLit q [225, 226, 227]) (countLit q [228, 229, 230, 231]) (count453 q) 1 (meaning445 q) (meaning453 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 453 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 232 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [232]) + (countLit q [233]) := List.countP_append (p := literal q) (l₁ := [232]) (l₂ := [233])
  have hm := merge_left (literal (valuationOf q) (232)) (literal (valuationOf q) (455)) (countLit q [232]) (countLit q [233]) (count455 q) 1 (meaning232 q) (meaning455 q) hs
  change valuationOf q 232 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 455 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [234]) + (countLit q [235]) := List.countP_append (p := literal q) (l₁ := [234]) (l₂ := [235])
  have hm := merge_left (literal (valuationOf q) (234)) (literal (valuationOf q) (457)) (countLit q [234]) (countLit q [235]) (count457 q) 1 (meaning234 q) (meaning457 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 457 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [232, 233]) + (countLit q [234, 235]) := List.countP_append (p := literal q) (l₁ := [232, 233]) (l₂ := [234, 235])
  have hm := merge_right (literal (valuationOf q) (457)) (literal (valuationOf q) (459)) (countLit q [232, 233]) (countLit q [234, 235]) (count459 q) 1 (meaning457 q) (meaning459 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 459 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [232, 233]) + (countLit q [234, 235]) := List.countP_append (p := literal q) (l₁ := [232, 233]) (l₂ := [234, 235])
  have hm := merge_left (literal (valuationOf q) (455)) (literal (valuationOf q) (459)) (countLit q [232, 233]) (countLit q [234, 235]) (count459 q) 1 (meaning455 q) (meaning459 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 459 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [232, 233]) + (countLit q [234, 235]) := List.countP_append (p := literal q) (l₁ := [232, 233]) (l₂ := [234, 235])
  have hm := merge_two (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (literal (valuationOf q) (460)) (countLit q [232, 233]) (countLit q [234, 235]) (count459 q) 1 1 (meaning455 q) (meaning457 q) (meaning460 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = false ∨ valuation q 460 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [236]) + (countLit q [238]) := List.countP_append (p := literal q) (l₁ := [236]) (l₂ := [238])
  have hm := merge_right (literal (valuationOf q) (238)) (literal (valuationOf q) (461)) (countLit q [236]) (countLit q [238]) (count461 q) 1 (meaning238 q) (meaning461 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 461 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [236, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [236, 238]) (l₂ := [239, 240])
  have hm := merge_left (literal (valuationOf q) (461)) (literal (valuationOf q) (465)) (countLit q [236, 238]) (countLit q [239, 240]) (count465 q) 1 (meaning461 q) (meaning465 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 465 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [232, 233, 234, 235]) + (countLit q [236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [232, 233, 234, 235]) (l₂ := [236, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [232, 233, 234, 235]) (countLit q [236, 238, 239, 240]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [232, 233, 234, 235]) + (countLit q [236, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [232, 233, 234, 235]) (l₂ := [236, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (459)) (literal (valuationOf q) (467)) (countLit q [232, 233, 234, 235]) (countLit q [236, 238, 239, 240]) (count467 q) 1 (meaning459 q) (meaning467 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 467 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E040.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112040
