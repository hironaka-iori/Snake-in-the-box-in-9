import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [235]) + (countLit q [236]) := List.countP_append (p := literal q) (l₁ := [235]) (l₂ := [236])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (455)) (countLit q [235]) (countLit q [236]) (count455 q) 1 (meaning235 q) (meaning455 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 455 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_right (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (countLit q [233, 234]) (countLit q [235, 236]) (count457 q) 1 (meaning455 q) (meaning457 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_left (literal (valuationOf q) (453)) (literal (valuationOf q) (457)) (countLit q [233, 234]) (countLit q [235, 236]) (count457 q) 1 (meaning453 q) (meaning457 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 457 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = false ∨ valuationOf q 458 = true := by
  have hs : count457 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_two (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (literal (valuationOf q) (458)) (countLit q [233, 234]) (countLit q [235, 236]) (count457 q) 1 1 (meaning453 q) (meaning455 q) (meaning458 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = false ∨ valuationOf q 458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = false ∨ valuation q 458 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (457)) (literal (valuationOf q) (459)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count459 q) 1 (meaning457 q) (meaning459 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 459 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 458 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (458)) (literal (valuationOf q) (460)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count459 q) 2 (meaning458 q) (meaning460 q) hs
  change valuationOf q 458 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 458 = false ∨ valuation q 460 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (451)) (literal (valuationOf q) (459)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count459 q) 1 (meaning451 q) (meaning459 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 459 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (451)) (literal (valuationOf q) (457)) (literal (valuationOf q) (460)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count459 q) 1 1 (meaning451 q) (meaning457 q) (meaning460 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 457 = false ∨ valuation q 460 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 452 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (452)) (literal (valuationOf q) (460)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count459 q) 2 (meaning452 q) (meaning460 q) hs
  change valuationOf q 452 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 452 = false ∨ valuation q 460 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (459)) (literal (valuationOf q) (461)) (countLit q [222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (count461 q) 1 (meaning459 q) (meaning461 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 460 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (460)) (literal (valuationOf q) (462)) (countLit q [222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (count461 q) 2 (meaning460 q) (meaning462 q) hs
  change valuationOf q 460 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 460 = false ∨ valuation q 462 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (445)) (literal (valuationOf q) (461)) (countLit q [222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (count461 q) 1 (meaning445 q) (meaning461 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 461 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 459 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (445)) (literal (valuationOf q) (459)) (literal (valuationOf q) (462)) (countLit q [222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (count461 q) 1 1 (meaning445 q) (meaning459 q) (meaning462 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 459 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 459 = false ∨ valuation q 462 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 446 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (446)) (literal (valuationOf q) (462)) (countLit q [222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (count461 q) 2 (meaning446 q) (meaning462 q) hs
  change valuationOf q 446 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 446 = false ∨ valuation q 462 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (461)) (literal (valuationOf q) (463)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 1 (meaning461 q) (meaning463 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 463 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 462 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (462)) (literal (valuationOf q) (464)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 2 (meaning462 q) (meaning464 q) hs
  change valuationOf q 462 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 462 = false ∨ valuation q 464 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (433)) (literal (valuationOf q) (463)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 1 (meaning433 q) (meaning463 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 463 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (433)) (literal (valuationOf q) (461)) (literal (valuationOf q) (464)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 1 1 (meaning433 q) (meaning461 q) (meaning464 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 461 = false ∨ valuation q 464 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 434 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (434)) (literal (valuationOf q) (464)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 2 (meaning434 q) (meaning464 q) hs
  change valuationOf q 434 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 434 = false ∨ valuation q 464 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (463)) (literal (valuationOf q) (465)) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 (meaning463 q) (meaning465 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 465 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 464 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (464)) (literal (valuationOf q) (466)) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 2 (meaning464 q) (meaning466 q) hs
  change valuationOf q 464 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 464 = false ∨ valuation q 466 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (465)) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 (meaning405 q) (meaning465 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 465 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (405)) (literal (valuationOf q) (463)) (literal (valuationOf q) (466)) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 1 (meaning405 q) (meaning463 q) (meaning466 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 463 = false ∨ valuation q 466 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 406 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (406)) (literal (valuationOf q) (466)) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 2 (meaning406 q) (meaning466 q) hs
  change valuationOf q 406 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 406 = false ∨ valuation q 466 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 466 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (466)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 2 (meaning466 q) (meaning468 q) hs
  change valuationOf q 466 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 466 = false ∨ valuation q 468 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (349)) (literal (valuationOf q) (465)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 1 1 (meaning349 q) (meaning465 q) (meaning468 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 465 = false ∨ valuation q 468 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 350 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (350)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 2 (meaning350 q) (meaning468 q) hs
  change valuationOf q 350 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 350 = false ∨ valuation q 468 = true := counterClause923 (baseVal q)

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 468 = false := by
  rw [value468]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count467 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 121 = true ∨ valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 124 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 212 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true ∨ valuation q 223 = true ∨ valuation q 224 = true ∨ valuation q 225 = true ∨ valuation q 226 = true ∨ valuation q 227 = true ∨ valuation q 228 = true ∨ valuation q 229 = true ∨ valuation q 230 = true ∨ valuation q 231 = true ∨ valuation q 232 = true ∨ valuation q 233 = true ∨ valuation q 234 = true ∨ valuation q 235 = true ∨ valuation q 236 = true := by
  rw [value119, value120, value121, value122, value123, value124, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value212, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222, value223, value224, value225, value226, value227, value228, value229, value230, value231, value232, value233, value234, value235, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause926 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-3]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1437)) (countLit q [-3]) (countLit q [-7]) (count1437 q) 1 (meaningNeg7 q) (meaning1437 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1437 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-3]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1437)) (countLit q [-3]) (countLit q [-7]) (count1437 q) 1 (meaningNeg3 q) (meaning1437 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1437 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1438 = true := by
  have hs : count1437 q = (countLit q [-3]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1438)) (countLit q [-3]) (countLit q [-7]) (count1437 q) 1 1 (meaningNeg3 q) (meaningNeg7 q) (meaning1438 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 7 = true ∨ valuation q 1438 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E027.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112027
