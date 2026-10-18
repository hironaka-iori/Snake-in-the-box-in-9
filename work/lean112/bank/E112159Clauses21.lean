import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 866 = false ∨ valuationOf q 871 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (866)) (literal (valuationOf q) (871)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 1 3 (meaning857 q) (meaning866 q) (meaning871 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 866 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 866 = false ∨ valuation q 871 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 867 = false ∨ valuationOf q 872 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (867)) (literal (valuationOf q) (872)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 1 4 (meaning857 q) (meaning867 q) (meaning872 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 867 = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 867 = false ∨ valuation q 872 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 869 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_left (literal (valuationOf q) (858)) (literal (valuationOf q) (869)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 2 (meaning858 q) (meaning869 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 869 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 864 = false ∨ valuationOf q 870 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (864)) (literal (valuationOf q) (870)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 2 1 (meaning858 q) (meaning864 q) (meaning870 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 864 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 864 = false ∨ valuation q 870 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 865 = false ∨ valuationOf q 871 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (865)) (literal (valuationOf q) (871)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 2 2 (meaning858 q) (meaning865 q) (meaning871 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 865 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 865 = false ∨ valuation q 871 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 866 = false ∨ valuationOf q 872 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (866)) (literal (valuationOf q) (872)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 2 3 (meaning858 q) (meaning866 q) (meaning872 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 866 = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 866 = false ∨ valuation q 872 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 864 = false ∨ valuationOf q 871 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_two (literal (valuationOf q) (859)) (literal (valuationOf q) (864)) (literal (valuationOf q) (871)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 3 1 (meaning859 q) (meaning864 q) (meaning871 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 864 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 864 = false ∨ valuation q 871 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-41]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (875)) (countLit q [-41]) (countLit q [-45]) (count875 q) 1 (meaningNeg45 q) (meaning875 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 875 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-41]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (875)) (countLit q [-41]) (countLit q [-45]) (count875 q) 1 (meaningNeg41 q) (meaning875 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 875 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 45 = true ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-41]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (876)) (countLit q [-41]) (countLit q [-45]) (count875 q) 1 1 (meaningNeg41 q) (meaningNeg45 q) (meaning876 q) hs
  change (! (valuationOf q 41)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 45 = true ∨ valuation q 876 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 877 = true := by
  have hs : count877 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (877)) (countLit q [-46]) (countLit q [-49]) (count877 q) 1 (meaningNeg49 q) (meaning877 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 877 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 877 = true := by
  have hs : count877 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (877)) (countLit q [-46]) (countLit q [-49]) (count877 q) 1 (meaningNeg46 q) (meaning877 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 877 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 49 = true ∨ valuationOf q 878 = true := by
  have hs : count877 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (878)) (countLit q [-46]) (countLit q [-49]) (count877 q) 1 1 (meaningNeg46 q) (meaningNeg49 q) (meaning878 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 49 = true ∨ valuation q 878 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-41, -45]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-41, -45]) (l₂ := [-46, -49])
  have hm := merge_right (literal (valuationOf q) (877)) (literal (valuationOf q) (879)) (countLit q [-41, -45]) (countLit q [-46, -49]) (count879 q) 1 (meaning877 q) (meaning879 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 879 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-41, -45]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-41, -45]) (l₂ := [-46, -49])
  have hm := merge_right (literal (valuationOf q) (878)) (literal (valuationOf q) (880)) (countLit q [-41, -45]) (countLit q [-46, -49]) (count879 q) 2 (meaning878 q) (meaning880 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 880 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-41, -45]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-41, -45]) (l₂ := [-46, -49])
  have hm := merge_left (literal (valuationOf q) (875)) (literal (valuationOf q) (879)) (countLit q [-41, -45]) (countLit q [-46, -49]) (count879 q) 1 (meaning875 q) (meaning879 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 879 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 877 = false ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-41, -45]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-41, -45]) (l₂ := [-46, -49])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (877)) (literal (valuationOf q) (880)) (countLit q [-41, -45]) (countLit q [-46, -49]) (count879 q) 1 1 (meaning875 q) (meaning877 q) (meaning880 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 877 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 877 = false ∨ valuation q 880 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 878 = false ∨ valuationOf q 881 = true := by
  have hs : count879 q = (countLit q [-41, -45]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-41, -45]) (l₂ := [-46, -49])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (878)) (literal (valuationOf q) (881)) (countLit q [-41, -45]) (countLit q [-46, -49]) (count879 q) 1 2 (meaning875 q) (meaning878 q) (meaning881 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 878 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 878 = false ∨ valuation q 881 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-41, -45]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-41, -45]) (l₂ := [-46, -49])
  have hm := merge_left (literal (valuationOf q) (876)) (literal (valuationOf q) (880)) (countLit q [-41, -45]) (countLit q [-46, -49]) (count879 q) 2 (meaning876 q) (meaning880 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 880 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 877 = false ∨ valuationOf q 881 = true := by
  have hs : count879 q = (countLit q [-41, -45]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-41, -45]) (l₂ := [-46, -49])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (877)) (literal (valuationOf q) (881)) (countLit q [-41, -45]) (countLit q [-46, -49]) (count879 q) 2 1 (meaning876 q) (meaning877 q) (meaning881 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 877 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 877 = false ∨ valuation q 881 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 878 = false ∨ valuationOf q 882 = true := by
  have hs : count879 q = (countLit q [-41, -45]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-41, -45]) (l₂ := [-46, -49])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (878)) (literal (valuationOf q) (882)) (countLit q [-41, -45]) (countLit q [-46, -49]) (count879 q) 2 2 (meaning876 q) (meaning878 q) (meaning882 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 878 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 878 = false ∨ valuation q 882 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (883)) (countLit q [-50]) (countLit q [-51]) (count883 q) 1 (meaningNeg51 q) (meaning883 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 883 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (883)) (countLit q [-50]) (countLit q [-51]) (count883 q) 1 (meaningNeg50 q) (meaning883 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 883 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 51 = true ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (884)) (countLit q [-50]) (countLit q [-51]) (count883 q) 1 1 (meaningNeg50 q) (meaningNeg51 q) (meaning884 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 884 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 885 = true := by
  have hs : count885 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (885)) (countLit q [-54]) (countLit q [-55]) (count885 q) 1 (meaningNeg54 q) (meaning885 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 885 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 55 = true ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (886)) (countLit q [-54]) (countLit q [-55]) (count885 q) 1 1 (meaningNeg54 q) (meaningNeg55 q) (meaning886 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 886 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 887 = true := by
  have hs : count887 q = (countLit q [-50, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -55])
  have hm := merge_right (literal (valuationOf q) (885)) (literal (valuationOf q) (887)) (countLit q [-50, -51]) (countLit q [-54, -55]) (count887 q) 1 (meaning885 q) (meaning887 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 887 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-50, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -55])
  have hm := merge_right (literal (valuationOf q) (886)) (literal (valuationOf q) (888)) (countLit q [-50, -51]) (countLit q [-54, -55]) (count887 q) 2 (meaning886 q) (meaning888 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 888 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 885 = false ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-50, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -55])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (885)) (literal (valuationOf q) (888)) (countLit q [-50, -51]) (countLit q [-54, -55]) (count887 q) 1 1 (meaning883 q) (meaning885 q) (meaning888 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 885 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 885 = false ∨ valuation q 888 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 886 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-50, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -55])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (886)) (literal (valuationOf q) (889)) (countLit q [-50, -51]) (countLit q [-54, -55]) (count887 q) 1 2 (meaning883 q) (meaning886 q) (meaning889 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 886 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 886 = false ∨ valuation q 889 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-50, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -55])
  have hm := merge_left (literal (valuationOf q) (884)) (literal (valuationOf q) (888)) (countLit q [-50, -51]) (countLit q [-54, -55]) (count887 q) 2 (meaning884 q) (meaning888 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 888 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 885 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-50, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -55])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (885)) (literal (valuationOf q) (889)) (countLit q [-50, -51]) (countLit q [-54, -55]) (count887 q) 2 1 (meaning884 q) (meaning885 q) (meaning889 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 885 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 885 = false ∨ valuation q 889 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E159.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112159
