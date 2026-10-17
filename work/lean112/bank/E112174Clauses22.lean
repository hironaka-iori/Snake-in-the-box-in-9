import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 850 = true := by
  have hs : count850 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (850)) (countLit q [-88]) (countLit q [-89]) (count850 q) 1 (meaningNeg89 q) (meaning850 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 850 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 850 = true := by
  have hs : count850 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (850)) (countLit q [-88]) (countLit q [-89]) (count850 q) 1 (meaningNeg88 q) (meaning850 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 850 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 852 = true := by
  have hs : count852 q = (countLit q [-86]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -89])
  have hm := merge_right (literal (valuationOf q) (850)) (literal (valuationOf q) (852)) (countLit q [-86]) (countLit q [-88, -89]) (count852 q) 1 (meaning850 q) (meaning852 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 852 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 852 = true := by
  have hs : count852 q = (countLit q [-86]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -89])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (852)) (countLit q [-86]) (countLit q [-88, -89]) (count852 q) 1 (meaningNeg86 q) (meaning852 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 852 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 850 = false ∨ valuationOf q 853 = true := by
  have hs : count852 q = (countLit q [-86]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -89])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (850)) (literal (valuationOf q) (853)) (countLit q [-86]) (countLit q [-88, -89]) (count852 q) 1 1 (meaningNeg86 q) (meaning850 q) (meaning853 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 850 = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 850 = false ∨ valuation q 853 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 855 = true := by
  have hs : count855 q = (countLit q [-81, -82, -84]) + (countLit q [-86, -88, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-86, -88, -89])
  have hm := merge_right (literal (valuationOf q) (852)) (literal (valuationOf q) (855)) (countLit q [-81, -82, -84]) (countLit q [-86, -88, -89]) (count855 q) 1 (meaning852 q) (meaning855 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 855 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 856 = true := by
  have hs : count855 q = (countLit q [-81, -82, -84]) + (countLit q [-86, -88, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-86, -88, -89])
  have hm := merge_right (literal (valuationOf q) (853)) (literal (valuationOf q) (856)) (countLit q [-81, -82, -84]) (countLit q [-86, -88, -89]) (count855 q) 2 (meaning853 q) (meaning856 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 856 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 855 = true := by
  have hs : count855 q = (countLit q [-81, -82, -84]) + (countLit q [-86, -88, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-86, -88, -89])
  have hm := merge_left (literal (valuationOf q) (847)) (literal (valuationOf q) (855)) (countLit q [-81, -82, -84]) (countLit q [-86, -88, -89]) (count855 q) 1 (meaning847 q) (meaning855 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 855 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 852 = false ∨ valuationOf q 856 = true := by
  have hs : count855 q = (countLit q [-81, -82, -84]) + (countLit q [-86, -88, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-86, -88, -89])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (852)) (literal (valuationOf q) (856)) (countLit q [-81, -82, -84]) (countLit q [-86, -88, -89]) (count855 q) 1 1 (meaning847 q) (meaning852 q) (meaning856 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 852 = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 852 = false ∨ valuation q 856 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 853 = false ∨ valuationOf q 857 = true := by
  have hs : count855 q = (countLit q [-81, -82, -84]) + (countLit q [-86, -88, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-86, -88, -89])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (853)) (literal (valuationOf q) (857)) (countLit q [-81, -82, -84]) (countLit q [-86, -88, -89]) (count855 q) 1 2 (meaning847 q) (meaning853 q) (meaning857 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 853 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 853 = false ∨ valuation q 857 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 861 = true := by
  have hs : count861 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (861)) (countLit q [-94]) (countLit q [-96]) (count861 q) 1 (meaningNeg96 q) (meaning861 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 861 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 861 = true := by
  have hs : count861 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (861)) (countLit q [-94]) (countLit q [-96]) (count861 q) 1 (meaningNeg94 q) (meaning861 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 861 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 863 = true := by
  have hs : count863 q = (countLit q [-91]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94, -96])
  have hm := merge_right (literal (valuationOf q) (861)) (literal (valuationOf q) (863)) (countLit q [-91]) (countLit q [-94, -96]) (count863 q) 1 (meaning861 q) (meaning863 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 863 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 866 = true := by
  have hs : count866 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (866)) (countLit q [-97]) (countLit q [-99]) (count866 q) 1 (meaningNeg97 q) (meaning866 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 866 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 868 = true := by
  have hs : count868 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (868)) (countLit q [-102]) (countLit q [-104]) (count868 q) 1 (meaningNeg104 q) (meaning868 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 868 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 868 = true := by
  have hs : count868 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (868)) (countLit q [-102]) (countLit q [-104]) (count868 q) 1 (meaningNeg102 q) (meaning868 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 868 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 870 = true := by
  have hs : count870 q = (countLit q [-97, -99]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-102, -104])
  have hm := merge_right (literal (valuationOf q) (868)) (literal (valuationOf q) (870)) (countLit q [-97, -99]) (countLit q [-102, -104]) (count870 q) 1 (meaning868 q) (meaning870 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 870 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 870 = true := by
  have hs : count870 q = (countLit q [-97, -99]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-102, -104])
  have hm := merge_left (literal (valuationOf q) (866)) (literal (valuationOf q) (870)) (countLit q [-97, -99]) (countLit q [-102, -104]) (count870 q) 1 (meaning866 q) (meaning870 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 870 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 868 = false ∨ valuationOf q 871 = true := by
  have hs : count870 q = (countLit q [-97, -99]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-102, -104])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (868)) (literal (valuationOf q) (871)) (countLit q [-97, -99]) (countLit q [-102, -104]) (count870 q) 1 1 (meaning866 q) (meaning868 q) (meaning871 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 868 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 868 = false ∨ valuation q 871 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 874 = true := by
  have hs : count874 q = (countLit q [-91, -94, -96]) + (countLit q [-97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-91, -94, -96]) (l₂ := [-97, -99, -102, -104])
  have hm := merge_right (literal (valuationOf q) (870)) (literal (valuationOf q) (874)) (countLit q [-91, -94, -96]) (countLit q [-97, -99, -102, -104]) (count874 q) 1 (meaning870 q) (meaning874 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 874 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 875 = true := by
  have hs : count874 q = (countLit q [-91, -94, -96]) + (countLit q [-97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-91, -94, -96]) (l₂ := [-97, -99, -102, -104])
  have hm := merge_right (literal (valuationOf q) (871)) (literal (valuationOf q) (875)) (countLit q [-91, -94, -96]) (countLit q [-97, -99, -102, -104]) (count874 q) 2 (meaning871 q) (meaning875 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 875 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 874 = true := by
  have hs : count874 q = (countLit q [-91, -94, -96]) + (countLit q [-97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-91, -94, -96]) (l₂ := [-97, -99, -102, -104])
  have hm := merge_left (literal (valuationOf q) (863)) (literal (valuationOf q) (874)) (countLit q [-91, -94, -96]) (countLit q [-97, -99, -102, -104]) (count874 q) 1 (meaning863 q) (meaning874 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 874 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 871 = false ∨ valuationOf q 876 = true := by
  have hs : count874 q = (countLit q [-91, -94, -96]) + (countLit q [-97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-91, -94, -96]) (l₂ := [-97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (871)) (literal (valuationOf q) (876)) (countLit q [-91, -94, -96]) (countLit q [-97, -99, -102, -104]) (count874 q) 1 2 (meaning863 q) (meaning871 q) (meaning876 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 871 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 871 = false ∨ valuation q 876 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-81, -82, -84, -86, -88, -89]) + (countLit q [-91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -88, -89]) (l₂ := [-91, -94, -96, -97, -99, -102, -104])
  have hm := merge_right (literal (valuationOf q) (874)) (literal (valuationOf q) (881)) (countLit q [-81, -82, -84, -86, -88, -89]) (countLit q [-91, -94, -96, -97, -99, -102, -104]) (count881 q) 1 (meaning874 q) (meaning881 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 881 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-81, -82, -84, -86, -88, -89]) + (countLit q [-91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -88, -89]) (l₂ := [-91, -94, -96, -97, -99, -102, -104])
  have hm := merge_left (literal (valuationOf q) (855)) (literal (valuationOf q) (881)) (countLit q [-81, -82, -84, -86, -88, -89]) (countLit q [-91, -94, -96, -97, -99, -102, -104]) (count881 q) 1 (meaning855 q) (meaning881 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 881 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 874 = false ∨ valuationOf q 882 = true := by
  have hs : count881 q = (countLit q [-81, -82, -84, -86, -88, -89]) + (countLit q [-91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -88, -89]) (l₂ := [-91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (874)) (literal (valuationOf q) (882)) (countLit q [-81, -82, -84, -86, -88, -89]) (countLit q [-91, -94, -96, -97, -99, -102, -104]) (count881 q) 1 1 (meaning855 q) (meaning874 q) (meaning882 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 874 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 874 = false ∨ valuation q 882 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 882 = true := by
  have hs : count881 q = (countLit q [-81, -82, -84, -86, -88, -89]) + (countLit q [-91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -88, -89]) (l₂ := [-91, -94, -96, -97, -99, -102, -104])
  have hm := merge_left (literal (valuationOf q) (856)) (literal (valuationOf q) (882)) (countLit q [-81, -82, -84, -86, -88, -89]) (countLit q [-91, -94, -96, -97, -99, -102, -104]) (count881 q) 2 (meaning856 q) (meaning882 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 882 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 874 = false ∨ valuationOf q 883 = true := by
  have hs : count881 q = (countLit q [-81, -82, -84, -86, -88, -89]) + (countLit q [-91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -88, -89]) (l₂ := [-91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (874)) (literal (valuationOf q) (883)) (countLit q [-81, -82, -84, -86, -88, -89]) (countLit q [-91, -94, -96, -97, -99, -102, -104]) (count881 q) 2 1 (meaning856 q) (meaning874 q) (meaning883 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 874 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 874 = false ∨ valuation q 883 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 875 = false ∨ valuationOf q 884 = true := by
  have hs : count881 q = (countLit q [-81, -82, -84, -86, -88, -89]) + (countLit q [-91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -88, -89]) (l₂ := [-91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (875)) (literal (valuationOf q) (884)) (countLit q [-81, -82, -84, -86, -88, -89]) (countLit q [-91, -94, -96, -97, -99, -102, -104]) (count881 q) 2 2 (meaning856 q) (meaning875 q) (meaning884 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 875 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 875 = false ∨ valuation q 884 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 876 = false ∨ valuationOf q 885 = true := by
  have hs : count881 q = (countLit q [-81, -82, -84, -86, -88, -89]) + (countLit q [-91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -88, -89]) (l₂ := [-91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (876)) (literal (valuationOf q) (885)) (countLit q [-81, -82, -84, -86, -88, -89]) (countLit q [-91, -94, -96, -97, -99, -102, -104]) (count881 q) 2 3 (meaning856 q) (meaning876 q) (meaning885 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 876 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 876 = false ∨ valuation q 885 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 883 = true := by
  have hs : count881 q = (countLit q [-81, -82, -84, -86, -88, -89]) + (countLit q [-91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -88, -89]) (l₂ := [-91, -94, -96, -97, -99, -102, -104])
  have hm := merge_left (literal (valuationOf q) (857)) (literal (valuationOf q) (883)) (countLit q [-81, -82, -84, -86, -88, -89]) (countLit q [-91, -94, -96, -97, -99, -102, -104]) (count881 q) 3 (meaning857 q) (meaning883 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 883 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 874 = false ∨ valuationOf q 884 = true := by
  have hs : count881 q = (countLit q [-81, -82, -84, -86, -88, -89]) + (countLit q [-91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -88, -89]) (l₂ := [-91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (874)) (literal (valuationOf q) (884)) (countLit q [-81, -82, -84, -86, -88, -89]) (countLit q [-91, -94, -96, -97, -99, -102, -104]) (count881 q) 3 1 (meaning857 q) (meaning874 q) (meaning884 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 874 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 874 = false ∨ valuation q 884 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E174.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112174
