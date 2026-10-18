import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 214 = false ∨ valuationOf q 215 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_two (literal (valuationOf q) (214)) (literal (valuationOf q) (215)) (literal (valuationOf q) (420)) (countLit q [214]) (countLit q [215]) (count419 q) 1 1 (meaning214 q) (meaning215 q) (meaning420 q) hs
  change valuationOf q 214 = false ∨ valuationOf q 215 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 215 = false ∨ valuation q 420 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 216 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [216]) + (countLit q [217]) := List.countP_append (p := literal q) (l₁ := [216]) (l₂ := [217])
  have hm := merge_left (literal (valuationOf q) (216)) (literal (valuationOf q) (421)) (countLit q [216]) (countLit q [217]) (count421 q) 1 (meaning216 q) (meaning421 q) hs
  change valuationOf q 216 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 421 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_right (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (countLit q [214, 215]) (countLit q [216, 217]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (423)) (countLit q [214, 215]) (countLit q [216, 217]) (count423 q) 1 (meaning419 q) (meaning423 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 423 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 421 = false ∨ valuationOf q 424 = true := by
  have hs : count423 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_two (literal (valuationOf q) (419)) (literal (valuationOf q) (421)) (literal (valuationOf q) (424)) (countLit q [214, 215]) (countLit q [216, 217]) (count423 q) 1 1 (meaning419 q) (meaning421 q) (meaning424 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 421 = false ∨ valuationOf q 424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 421 = false ∨ valuation q 424 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 420 = false ∨ valuationOf q 424 = true := by
  have hs : count423 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_left (literal (valuationOf q) (420)) (literal (valuationOf q) (424)) (countLit q [214, 215]) (countLit q [216, 217]) (count423 q) 2 (meaning420 q) (meaning424 q) hs
  change valuationOf q 420 = false ∨ valuationOf q 424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 420 = false ∨ valuation q 424 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [220]) + (countLit q [221]) := List.countP_append (p := literal q) (l₁ := [220]) (l₂ := [221])
  have hm := merge_left (literal (valuationOf q) (220)) (literal (valuationOf q) (427)) (countLit q [220]) (countLit q [221]) (count427 q) 1 (meaning220 q) (meaning427 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 427 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [218, 219]) + (countLit q [220, 221]) := List.countP_append (p := literal q) (l₁ := [218, 219]) (l₂ := [220, 221])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [218, 219]) (countLit q [220, 221]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (423)) (literal (valuationOf q) (431)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 1 (meaning423 q) (meaning431 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 431 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_two (literal (valuationOf q) (423)) (literal (valuationOf q) (429)) (literal (valuationOf q) (432)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 1 1 (meaning423 q) (meaning429 q) (meaning432 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 429 = false ∨ valuation q 432 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 424 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (424)) (literal (valuationOf q) (432)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 2 (meaning424 q) (meaning432 q) hs
  change valuationOf q 424 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 424 = false ∨ valuation q 432 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (431)) (literal (valuationOf q) (433)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 1 (meaning431 q) (meaning433 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 433 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 432 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (432)) (literal (valuationOf q) (434)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 2 (meaning432 q) (meaning434 q) hs
  change valuationOf q 432 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 432 = false ∨ valuation q 434 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (433)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 1 (meaning417 q) (meaning433 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 433 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_two (literal (valuationOf q) (417)) (literal (valuationOf q) (431)) (literal (valuationOf q) (434)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 1 1 (meaning417 q) (meaning431 q) (meaning434 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 431 = false ∨ valuation q 434 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (418)) (literal (valuationOf q) (434)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 2 (meaning418 q) (meaning434 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 434 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 224 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [223]) + (countLit q [224]) := List.countP_append (p := literal q) (l₁ := [223]) (l₂ := [224])
  have hm := merge_right (literal (valuationOf q) (224)) (literal (valuationOf q) (435)) (countLit q [223]) (countLit q [224]) (count435 q) 1 (meaning224 q) (meaning435 q) hs
  change valuationOf q 224 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 224 = false ∨ valuation q 435 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [223]) + (countLit q [224]) := List.countP_append (p := literal q) (l₁ := [223]) (l₂ := [224])
  have hm := merge_left (literal (valuationOf q) (223)) (literal (valuationOf q) (435)) (countLit q [223]) (countLit q [224]) (count435 q) 1 (meaning223 q) (meaning435 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 435 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [222]) (l₂ := [223, 224])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [222]) (countLit q [223, 224]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [222]) (l₂ := [223, 224])
  have hm := merge_left (literal (valuationOf q) (222)) (literal (valuationOf q) (437)) (countLit q [222]) (countLit q [223, 224]) (count437 q) 1 (meaning222 q) (meaning437 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 437 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_right (literal (valuationOf q) (226)) (literal (valuationOf q) (439)) (countLit q [225]) (countLit q [226]) (count439 q) 1 (meaning226 q) (meaning439 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 439 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_left (literal (valuationOf q) (439)) (literal (valuationOf q) (443)) (countLit q [225, 226]) (countLit q [227, 228]) (count443 q) 1 (meaning439 q) (meaning443 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 443 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (countLit q [222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (445)) (countLit q [222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 (meaning437 q) (meaning445 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 445 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 443 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_two (literal (valuationOf q) (437)) (literal (valuationOf q) (443)) (literal (valuationOf q) (446)) (countLit q [222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 1 (meaning437 q) (meaning443 q) (meaning446 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 443 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 443 = false ∨ valuation q 446 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal q) (l₁ := [229]) (l₂ := [230])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (447)) (countLit q [229]) (countLit q [230]) (count447 q) 1 (meaning229 q) (meaning447 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 447 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 232 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_right (literal (valuationOf q) (232)) (literal (valuationOf q) (449)) (countLit q [231]) (countLit q [232]) (count449 q) 1 (meaning232 q) (meaning449 q) hs
  change valuationOf q 232 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 449 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_right (literal (valuationOf q) (449)) (literal (valuationOf q) (451)) (countLit q [229, 230]) (countLit q [231, 232]) (count451 q) 1 (meaning449 q) (meaning451 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 451 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_left (literal (valuationOf q) (447)) (literal (valuationOf q) (451)) (countLit q [229, 230]) (countLit q [231, 232]) (count451 q) 1 (meaning447 q) (meaning451 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 451 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 449 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_two (literal (valuationOf q) (447)) (literal (valuationOf q) (449)) (literal (valuationOf q) (452)) (countLit q [229, 230]) (countLit q [231, 232]) (count451 q) 1 1 (meaning447 q) (meaning449 q) (meaning452 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 449 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 449 = false ∨ valuation q 452 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (453)) (countLit q [233]) (countLit q [234]) (count453 q) 1 (meaning233 q) (meaning453 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 453 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E027.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112027
