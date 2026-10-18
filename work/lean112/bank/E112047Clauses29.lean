import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (423)) (countLit q [214, 215]) (countLit q [216, 217]) (count423 q) 1 (meaning419 q) (meaning423 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 423 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 420 = false ∨ valuationOf q 424 = true := by
  have hs : count423 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_left (literal (valuationOf q) (420)) (literal (valuationOf q) (424)) (countLit q [214, 215]) (countLit q [216, 217]) (count423 q) 2 (meaning420 q) (meaning424 q) hs
  change valuationOf q 420 = false ∨ valuationOf q 424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 420 = false ∨ valuation q 424 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [218]) + (countLit q [219]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (425)) (countLit q [218]) (countLit q [219]) (count425 q) 1 (meaning219 q) (meaning425 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 425 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [220]) + (countLit q [221]) := List.countP_append (p := literal q) (l₁ := [220]) (l₂ := [221])
  have hm := merge_right (literal (valuationOf q) (221)) (literal (valuationOf q) (427)) (countLit q [220]) (countLit q [221]) (count427 q) 1 (meaning221 q) (meaning427 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 427 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [218, 219]) + (countLit q [220, 221]) := List.countP_append (p := literal q) (l₁ := [218, 219]) (l₂ := [220, 221])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [218, 219]) (countLit q [220, 221]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [218, 219]) + (countLit q [220, 221]) := List.countP_append (p := literal q) (l₁ := [218, 219]) (l₂ := [220, 221])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (429)) (countLit q [218, 219]) (countLit q [220, 221]) (count429 q) 1 (meaning425 q) (meaning429 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 429 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [218, 219]) + (countLit q [220, 221]) := List.countP_append (p := literal q) (l₁ := [218, 219]) (l₂ := [220, 221])
  have hm := merge_two (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (literal (valuationOf q) (430)) (countLit q [218, 219]) (countLit q [220, 221]) (count429 q) 1 1 (meaning425 q) (meaning427 q) (meaning430 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = false ∨ valuation q 430 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 430 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (430)) (literal (valuationOf q) (432)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 2 (meaning430 q) (meaning432 q) hs
  change valuationOf q 430 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 430 = false ∨ valuation q 432 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (423)) (literal (valuationOf q) (431)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 1 (meaning423 q) (meaning431 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 431 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_two (literal (valuationOf q) (423)) (literal (valuationOf q) (429)) (literal (valuationOf q) (432)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 1 1 (meaning423 q) (meaning429 q) (meaning432 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 429 = false ∨ valuation q 432 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 424 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (424)) (literal (valuationOf q) (432)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 2 (meaning424 q) (meaning432 q) hs
  change valuationOf q 424 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 424 = false ∨ valuation q 432 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (431)) (literal (valuationOf q) (433)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 1 (meaning431 q) (meaning433 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 433 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 432 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (432)) (literal (valuationOf q) (434)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 2 (meaning432 q) (meaning434 q) hs
  change valuationOf q 432 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 432 = false ∨ valuation q 434 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (433)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 1 (meaning417 q) (meaning433 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 433 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_two (literal (valuationOf q) (417)) (literal (valuationOf q) (431)) (literal (valuationOf q) (434)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 1 1 (meaning417 q) (meaning431 q) (meaning434 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 431 = false ∨ valuation q 434 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (418)) (literal (valuationOf q) (434)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 2 (meaning418 q) (meaning434 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 434 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [223]) + (countLit q [224]) := List.countP_append (p := literal q) (l₁ := [223]) (l₂ := [224])
  have hm := merge_left (literal (valuationOf q) (223)) (literal (valuationOf q) (435)) (countLit q [223]) (countLit q [224]) (count435 q) 1 (meaning223 q) (meaning435 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 435 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [222]) (l₂ := [223, 224])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [222]) (countLit q [223, 224]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [222]) (l₂ := [223, 224])
  have hm := merge_left (literal (valuationOf q) (222)) (literal (valuationOf q) (437)) (countLit q [222]) (countLit q [223, 224]) (count437 q) 1 (meaning222 q) (meaning437 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 437 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_right (literal (valuationOf q) (226)) (literal (valuationOf q) (439)) (countLit q [225]) (countLit q [226]) (count439 q) 1 (meaning226 q) (meaning439 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 439 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [227]) + (countLit q [228]) := List.countP_append (p := literal q) (l₁ := [227]) (l₂ := [228])
  have hm := merge_right (literal (valuationOf q) (228)) (literal (valuationOf q) (441)) (countLit q [227]) (countLit q [228]) (count441 q) 1 (meaning228 q) (meaning441 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 441 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_right (literal (valuationOf q) (441)) (literal (valuationOf q) (443)) (countLit q [225, 226]) (countLit q [227, 228]) (count443 q) 1 (meaning441 q) (meaning443 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 443 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_left (literal (valuationOf q) (439)) (literal (valuationOf q) (443)) (countLit q [225, 226]) (countLit q [227, 228]) (count443 q) 1 (meaning439 q) (meaning443 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 443 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 441 = false ∨ valuationOf q 444 = true := by
  have hs : count443 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_two (literal (valuationOf q) (439)) (literal (valuationOf q) (441)) (literal (valuationOf q) (444)) (countLit q [225, 226]) (countLit q [227, 228]) (count443 q) 1 1 (meaning439 q) (meaning441 q) (meaning444 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 441 = false ∨ valuationOf q 444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 441 = false ∨ valuation q 444 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (countLit q [222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 444 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (444)) (literal (valuationOf q) (446)) (countLit q [222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 2 (meaning444 q) (meaning446 q) hs
  change valuationOf q 444 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 444 = false ∨ valuation q 446 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (445)) (countLit q [222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 (meaning437 q) (meaning445 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 445 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 443 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_two (literal (valuationOf q) (437)) (literal (valuationOf q) (443)) (literal (valuationOf q) (446)) (countLit q [222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 1 (meaning437 q) (meaning443 q) (meaning446 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 443 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 443 = false ∨ valuation q 446 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal q) (l₁ := [229]) (l₂ := [230])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (447)) (countLit q [229]) (countLit q [230]) (count447 q) 1 (meaning229 q) (meaning447 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 447 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (449)) (countLit q [231]) (countLit q [232]) (count449 q) 1 (meaning231 q) (meaning449 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 449 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_right (literal (valuationOf q) (449)) (literal (valuationOf q) (451)) (countLit q [229, 230]) (countLit q [231, 232]) (count451 q) 1 (meaning449 q) (meaning451 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 451 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E047.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112047
