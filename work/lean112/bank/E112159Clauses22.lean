import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 886 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-50, -51]) + (countLit q [-54, -55]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-54, -55])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (886)) (literal (valuationOf q) (890)) (countLit q [-50, -51]) (countLit q [-54, -55]) (count887 q) 2 2 (meaning884 q) (meaning886 q) (meaning890 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 886 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 886 = false ∨ valuation q 890 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 888 = false ∨ valuationOf q 892 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_right (literal (valuationOf q) (888)) (literal (valuationOf q) (892)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 2 (meaning888 q) (meaning892 q) hs
  change valuationOf q 888 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 888 = false ∨ valuation q 892 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 893 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_right (literal (valuationOf q) (889)) (literal (valuationOf q) (893)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 3 (meaning889 q) (meaning893 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 893 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 894 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_right (literal (valuationOf q) (890)) (literal (valuationOf q) (894)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 4 (meaning890 q) (meaning894 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 894 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 887 = false ∨ valuationOf q 892 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (887)) (literal (valuationOf q) (892)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 1 1 (meaning879 q) (meaning887 q) (meaning892 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 887 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 887 = false ∨ valuation q 892 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 888 = false ∨ valuationOf q 893 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (888)) (literal (valuationOf q) (893)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 1 2 (meaning879 q) (meaning888 q) (meaning893 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 888 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 888 = false ∨ valuation q 893 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 889 = false ∨ valuationOf q 894 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (889)) (literal (valuationOf q) (894)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 1 3 (meaning879 q) (meaning889 q) (meaning894 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 889 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 889 = false ∨ valuation q 894 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 890 = false ∨ valuationOf q 895 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (890)) (literal (valuationOf q) (895)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 1 4 (meaning879 q) (meaning890 q) (meaning895 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 890 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 890 = false ∨ valuation q 895 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 887 = false ∨ valuationOf q 893 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (887)) (literal (valuationOf q) (893)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 2 1 (meaning880 q) (meaning887 q) (meaning893 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 887 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 887 = false ∨ valuation q 893 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 888 = false ∨ valuationOf q 894 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (888)) (literal (valuationOf q) (894)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 2 2 (meaning880 q) (meaning888 q) (meaning894 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 888 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 888 = false ∨ valuation q 894 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 889 = false ∨ valuationOf q 895 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (889)) (literal (valuationOf q) (895)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 2 3 (meaning880 q) (meaning889 q) (meaning895 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 889 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 889 = false ∨ valuation q 895 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 890 = false ∨ valuationOf q 896 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (890)) (literal (valuationOf q) (896)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 2 4 (meaning880 q) (meaning890 q) (meaning896 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 890 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 890 = false ∨ valuation q 896 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 887 = false ∨ valuationOf q 894 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (887)) (literal (valuationOf q) (894)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 3 1 (meaning881 q) (meaning887 q) (meaning894 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 887 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 887 = false ∨ valuation q 894 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 888 = false ∨ valuationOf q 895 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (888)) (literal (valuationOf q) (895)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 3 2 (meaning881 q) (meaning888 q) (meaning895 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 888 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 888 = false ∨ valuation q 895 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 889 = false ∨ valuationOf q 896 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (889)) (literal (valuationOf q) (896)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 3 3 (meaning881 q) (meaning889 q) (meaning896 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 889 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 889 = false ∨ valuation q 896 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 890 = false ∨ valuationOf q 897 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (890)) (literal (valuationOf q) (897)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 3 4 (meaning881 q) (meaning890 q) (meaning897 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 890 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 890 = false ∨ valuation q 897 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 887 = false ∨ valuationOf q 895 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (887)) (literal (valuationOf q) (895)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 4 1 (meaning882 q) (meaning887 q) (meaning895 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 887 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 887 = false ∨ valuation q 895 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 888 = false ∨ valuationOf q 896 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (888)) (literal (valuationOf q) (896)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 4 2 (meaning882 q) (meaning888 q) (meaning896 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 888 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 888 = false ∨ valuation q 896 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 889 = false ∨ valuationOf q 897 = true := by
  have hs : count891 q = (countLit q [-41, -45, -46, -49]) + (countLit q [-50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -45, -46, -49]) (l₂ := [-50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (889)) (literal (valuationOf q) (897)) (countLit q [-41, -45, -46, -49]) (countLit q [-50, -51, -54, -55]) (count891 q) 4 3 (meaning882 q) (meaning889 q) (meaning897 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 889 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 889 = false ∨ valuation q 897 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 904 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_right (literal (valuationOf q) (896)) (literal (valuationOf q) (904)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 6 (meaning896 q) (meaning904 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 904 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 905 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_right (literal (valuationOf q) (897)) (literal (valuationOf q) (905)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 7 (meaning897 q) (meaning905 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 905 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 892 = false ∨ valuationOf q 901 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (892)) (literal (valuationOf q) (901)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 1 2 (meaning868 q) (meaning892 q) (meaning901 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 892 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 892 = false ∨ valuation q 901 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 893 = false ∨ valuationOf q 902 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (893)) (literal (valuationOf q) (902)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 1 3 (meaning868 q) (meaning893 q) (meaning902 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 893 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 893 = false ∨ valuation q 902 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 894 = false ∨ valuationOf q 903 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (894)) (literal (valuationOf q) (903)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 1 4 (meaning868 q) (meaning894 q) (meaning903 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 894 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 894 = false ∨ valuation q 903 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 895 = false ∨ valuationOf q 904 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (895)) (literal (valuationOf q) (904)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 1 5 (meaning868 q) (meaning895 q) (meaning904 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 895 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 895 = false ∨ valuation q 904 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 896 = false ∨ valuationOf q 905 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (896)) (literal (valuationOf q) (905)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 1 6 (meaning868 q) (meaning896 q) (meaning905 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 896 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 896 = false ∨ valuation q 905 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 897 = false ∨ valuationOf q 906 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (897)) (literal (valuationOf q) (906)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 1 7 (meaning868 q) (meaning897 q) (meaning906 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 897 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 897 = false ∨ valuation q 906 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 892 = false ∨ valuationOf q 902 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (892)) (literal (valuationOf q) (902)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 2 2 (meaning869 q) (meaning892 q) (meaning902 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 892 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 892 = false ∨ valuation q 902 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 893 = false ∨ valuationOf q 903 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (893)) (literal (valuationOf q) (903)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 2 3 (meaning869 q) (meaning893 q) (meaning903 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 893 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 893 = false ∨ valuation q 903 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 894 = false ∨ valuationOf q 904 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (894)) (literal (valuationOf q) (904)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 2 4 (meaning869 q) (meaning894 q) (meaning904 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 894 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 894 = false ∨ valuation q 904 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 895 = false ∨ valuationOf q 905 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (895)) (literal (valuationOf q) (905)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 2 5 (meaning869 q) (meaning895 q) (meaning905 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 895 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 895 = false ∨ valuation q 905 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 896 = false ∨ valuationOf q 906 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (896)) (literal (valuationOf q) (906)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 2 6 (meaning869 q) (meaning896 q) (meaning906 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 896 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 896 = false ∨ valuation q 906 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E159.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112159
