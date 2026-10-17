import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 808 = false ∨ valuationOf q 813 = true := by
  have hs : count810 q = (countLit q [-27, -29, -31]) + (countLit q [-32, -34, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-32, -34, -37, -39])
  have hm := merge_two (literal (valuationOf q) (799)) (literal (valuationOf q) (808)) (literal (valuationOf q) (813)) (countLit q [-27, -29, -31]) (countLit q [-32, -34, -37, -39]) (count810 q) 1 3 (meaning799 q) (meaning808 q) (meaning813 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 808 = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 808 = false ∨ valuation q 813 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 809 = false ∨ valuationOf q 814 = true := by
  have hs : count810 q = (countLit q [-27, -29, -31]) + (countLit q [-32, -34, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-32, -34, -37, -39])
  have hm := merge_two (literal (valuationOf q) (799)) (literal (valuationOf q) (809)) (literal (valuationOf q) (814)) (countLit q [-27, -29, -31]) (countLit q [-32, -34, -37, -39]) (count810 q) 1 4 (meaning799 q) (meaning809 q) (meaning814 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 809 = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 809 = false ∨ valuation q 814 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-27, -29, -31]) + (countLit q [-32, -34, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-32, -34, -37, -39])
  have hm := merge_left (literal (valuationOf q) (800)) (literal (valuationOf q) (811)) (countLit q [-27, -29, -31]) (countLit q [-32, -34, -37, -39]) (count810 q) 2 (meaning800 q) (meaning811 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 811 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 806 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-27, -29, -31]) + (countLit q [-32, -34, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-32, -34, -37, -39])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (806)) (literal (valuationOf q) (812)) (countLit q [-27, -29, -31]) (countLit q [-32, -34, -37, -39]) (count810 q) 2 1 (meaning800 q) (meaning806 q) (meaning812 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 806 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 806 = false ∨ valuation q 812 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 807 = false ∨ valuationOf q 813 = true := by
  have hs : count810 q = (countLit q [-27, -29, -31]) + (countLit q [-32, -34, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-32, -34, -37, -39])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (807)) (literal (valuationOf q) (813)) (countLit q [-27, -29, -31]) (countLit q [-32, -34, -37, -39]) (count810 q) 2 2 (meaning800 q) (meaning807 q) (meaning813 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 807 = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 807 = false ∨ valuation q 813 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-27, -29, -31]) + (countLit q [-32, -34, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-32, -34, -37, -39])
  have hm := merge_left (literal (valuationOf q) (801)) (literal (valuationOf q) (812)) (countLit q [-27, -29, -31]) (countLit q [-32, -34, -37, -39]) (count810 q) 3 (meaning801 q) (meaning812 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 812 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 817 = true := by
  have hs : count817 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (817)) (countLit q [-43]) (countLit q [-45]) (count817 q) 1 (meaningNeg45 q) (meaning817 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 817 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 817 = true := by
  have hs : count817 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (817)) (countLit q [-43]) (countLit q [-45]) (count817 q) 1 (meaningNeg43 q) (meaning817 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 817 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 45 = true ∨ valuationOf q 818 = true := by
  have hs : count817 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (818)) (countLit q [-43]) (countLit q [-45]) (count817 q) 1 1 (meaningNeg43 q) (meaningNeg45 q) (meaning818 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 45 = true ∨ valuation q 818 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 819 = true := by
  have hs : count819 q = (countLit q [-40]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -45])
  have hm := merge_right (literal (valuationOf q) (817)) (literal (valuationOf q) (819)) (countLit q [-40]) (countLit q [-43, -45]) (count819 q) 1 (meaning817 q) (meaning819 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 819 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 818 = false ∨ valuationOf q 820 = true := by
  have hs : count819 q = (countLit q [-40]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -45])
  have hm := merge_right (literal (valuationOf q) (818)) (literal (valuationOf q) (820)) (countLit q [-40]) (countLit q [-43, -45]) (count819 q) 2 (meaning818 q) (meaning820 q) hs
  change valuationOf q 818 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 818 = false ∨ valuation q 820 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 819 = true := by
  have hs : count819 q = (countLit q [-40]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -45])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (819)) (countLit q [-40]) (countLit q [-43, -45]) (count819 q) 1 (meaningNeg40 q) (meaning819 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 819 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 817 = false ∨ valuationOf q 820 = true := by
  have hs : count819 q = (countLit q [-40]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (817)) (literal (valuationOf q) (820)) (countLit q [-40]) (countLit q [-43, -45]) (count819 q) 1 1 (meaningNeg40 q) (meaning817 q) (meaning820 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 817 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 817 = false ∨ valuation q 820 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 822 = true := by
  have hs : count822 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (822)) (countLit q [-46]) (countLit q [-48]) (count822 q) 1 (meaningNeg46 q) (meaning822 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 822 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 824 = true := by
  have hs : count824 q = (countLit q [-51]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (824)) (countLit q [-51]) (countLit q [-53]) (count824 q) 1 (meaningNeg53 q) (meaning824 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 824 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 824 = true := by
  have hs : count824 q = (countLit q [-51]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (824)) (countLit q [-51]) (countLit q [-53]) (count824 q) 1 (meaningNeg51 q) (meaning824 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 824 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 53 = true ∨ valuationOf q 825 = true := by
  have hs : count824 q = (countLit q [-51]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (825)) (countLit q [-51]) (countLit q [-53]) (count824 q) 1 1 (meaningNeg51 q) (meaningNeg53 q) (meaning825 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 825 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 826 = true := by
  have hs : count826 q = (countLit q [-46, -48]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -53])
  have hm := merge_right (literal (valuationOf q) (824)) (literal (valuationOf q) (826)) (countLit q [-46, -48]) (countLit q [-51, -53]) (count826 q) 1 (meaning824 q) (meaning826 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 826 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-46, -48]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -53])
  have hm := merge_right (literal (valuationOf q) (825)) (literal (valuationOf q) (827)) (countLit q [-46, -48]) (countLit q [-51, -53]) (count826 q) 2 (meaning825 q) (meaning827 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 827 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 826 = true := by
  have hs : count826 q = (countLit q [-46, -48]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -53])
  have hm := merge_left (literal (valuationOf q) (822)) (literal (valuationOf q) (826)) (countLit q [-46, -48]) (countLit q [-51, -53]) (count826 q) 1 (meaning822 q) (meaning826 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 826 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 824 = false ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-46, -48]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -53])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (824)) (literal (valuationOf q) (827)) (countLit q [-46, -48]) (countLit q [-51, -53]) (count826 q) 1 1 (meaning822 q) (meaning824 q) (meaning827 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 824 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 824 = false ∨ valuation q 827 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 825 = false ∨ valuationOf q 828 = true := by
  have hs : count826 q = (countLit q [-46, -48]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -53])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (825)) (literal (valuationOf q) (828)) (countLit q [-46, -48]) (countLit q [-51, -53]) (count826 q) 1 2 (meaning822 q) (meaning825 q) (meaning828 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 825 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 825 = false ∨ valuation q 828 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 830 = true := by
  have hs : count830 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -48, -51, -53])
  have hm := merge_right (literal (valuationOf q) (826)) (literal (valuationOf q) (830)) (countLit q [-40, -43, -45]) (countLit q [-46, -48, -51, -53]) (count830 q) 1 (meaning826 q) (meaning830 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 830 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -48, -51, -53])
  have hm := merge_right (literal (valuationOf q) (827)) (literal (valuationOf q) (831)) (countLit q [-40, -43, -45]) (countLit q [-46, -48, -51, -53]) (count830 q) 2 (meaning827 q) (meaning831 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 831 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -48, -51, -53])
  have hm := merge_right (literal (valuationOf q) (828)) (literal (valuationOf q) (832)) (countLit q [-40, -43, -45]) (countLit q [-46, -48, -51, -53]) (count830 q) 3 (meaning828 q) (meaning832 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 832 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 830 = true := by
  have hs : count830 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -48, -51, -53])
  have hm := merge_left (literal (valuationOf q) (819)) (literal (valuationOf q) (830)) (countLit q [-40, -43, -45]) (countLit q [-46, -48, -51, -53]) (count830 q) 1 (meaning819 q) (meaning830 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 830 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 826 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (819)) (literal (valuationOf q) (826)) (literal (valuationOf q) (831)) (countLit q [-40, -43, -45]) (countLit q [-46, -48, -51, -53]) (count830 q) 1 1 (meaning819 q) (meaning826 q) (meaning831 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 826 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 826 = false ∨ valuation q 831 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 827 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (819)) (literal (valuationOf q) (827)) (literal (valuationOf q) (832)) (countLit q [-40, -43, -45]) (countLit q [-46, -48, -51, -53]) (count830 q) 1 2 (meaning819 q) (meaning827 q) (meaning832 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 827 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 827 = false ∨ valuation q 832 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -48, -51, -53])
  have hm := merge_left (literal (valuationOf q) (820)) (literal (valuationOf q) (831)) (countLit q [-40, -43, -45]) (countLit q [-46, -48, -51, -53]) (count830 q) 2 (meaning820 q) (meaning831 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 831 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 826 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (820)) (literal (valuationOf q) (826)) (literal (valuationOf q) (832)) (countLit q [-40, -43, -45]) (countLit q [-46, -48, -51, -53]) (count830 q) 2 1 (meaning820 q) (meaning826 q) (meaning832 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 826 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 826 = false ∨ valuation q 832 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 830 = false ∨ valuationOf q 838 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (830)) (literal (valuationOf q) (838)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 1 1 (meaning810 q) (meaning830 q) (meaning838 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 830 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 830 = false ∨ valuation q 838 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 832 = false ∨ valuationOf q 840 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (832)) (literal (valuationOf q) (840)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 1 3 (meaning810 q) (meaning832 q) (meaning840 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 832 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 832 = false ∨ valuation q 840 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E185.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112185
