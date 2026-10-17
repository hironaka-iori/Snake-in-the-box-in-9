import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 950 = true := by
  have hs : count950 q = (countLit q [-101, -103]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -103]) (l₂ := [-106, -108])
  have hm := merge_left (literal (valuationOf q) (946)) (literal (valuationOf q) (950)) (countLit q [-101, -103]) (countLit q [-106, -108]) (count950 q) 1 (meaning946 q) (meaning950 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 950 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 948 = false ∨ valuationOf q 951 = true := by
  have hs : count950 q = (countLit q [-101, -103]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -103]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (948)) (literal (valuationOf q) (951)) (countLit q [-101, -103]) (countLit q [-106, -108]) (count950 q) 1 1 (meaning946 q) (meaning948 q) (meaning951 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 948 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 948 = false ∨ valuation q 951 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 951 = true := by
  have hs : count950 q = (countLit q [-101, -103]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -103]) (l₂ := [-106, -108])
  have hm := merge_left (literal (valuationOf q) (947)) (literal (valuationOf q) (951)) (countLit q [-101, -103]) (countLit q [-106, -108]) (count950 q) 2 (meaning947 q) (meaning951 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 951 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 948 = false ∨ valuationOf q 952 = true := by
  have hs : count950 q = (countLit q [-101, -103]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -103]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (948)) (literal (valuationOf q) (952)) (countLit q [-101, -103]) (countLit q [-106, -108]) (count950 q) 2 1 (meaning947 q) (meaning948 q) (meaning952 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 948 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 948 = false ∨ valuation q 952 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 954 = true := by
  have hs : count954 q = (countLit q [-95, -98, -100]) + (countLit q [-101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -100]) (l₂ := [-101, -103, -106, -108])
  have hm := merge_right (literal (valuationOf q) (950)) (literal (valuationOf q) (954)) (countLit q [-95, -98, -100]) (countLit q [-101, -103, -106, -108]) (count954 q) 1 (meaning950 q) (meaning954 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 954 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 955 = true := by
  have hs : count954 q = (countLit q [-95, -98, -100]) + (countLit q [-101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -100]) (l₂ := [-101, -103, -106, -108])
  have hm := merge_right (literal (valuationOf q) (951)) (literal (valuationOf q) (955)) (countLit q [-95, -98, -100]) (countLit q [-101, -103, -106, -108]) (count954 q) 2 (meaning951 q) (meaning955 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 955 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 956 = true := by
  have hs : count954 q = (countLit q [-95, -98, -100]) + (countLit q [-101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -100]) (l₂ := [-101, -103, -106, -108])
  have hm := merge_right (literal (valuationOf q) (952)) (literal (valuationOf q) (956)) (countLit q [-95, -98, -100]) (countLit q [-101, -103, -106, -108]) (count954 q) 3 (meaning952 q) (meaning956 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 956 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 954 = true := by
  have hs : count954 q = (countLit q [-95, -98, -100]) + (countLit q [-101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -100]) (l₂ := [-101, -103, -106, -108])
  have hm := merge_left (literal (valuationOf q) (943)) (literal (valuationOf q) (954)) (countLit q [-95, -98, -100]) (countLit q [-101, -103, -106, -108]) (count954 q) 1 (meaning943 q) (meaning954 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 954 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 950 = false ∨ valuationOf q 955 = true := by
  have hs : count954 q = (countLit q [-95, -98, -100]) + (countLit q [-101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -100]) (l₂ := [-101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (950)) (literal (valuationOf q) (955)) (countLit q [-95, -98, -100]) (countLit q [-101, -103, -106, -108]) (count954 q) 1 1 (meaning943 q) (meaning950 q) (meaning955 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 950 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 950 = false ∨ valuation q 955 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 951 = false ∨ valuationOf q 956 = true := by
  have hs : count954 q = (countLit q [-95, -98, -100]) + (countLit q [-101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -100]) (l₂ := [-101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (951)) (literal (valuationOf q) (956)) (countLit q [-95, -98, -100]) (countLit q [-101, -103, -106, -108]) (count954 q) 1 2 (meaning943 q) (meaning951 q) (meaning956 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 951 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 951 = false ∨ valuation q 956 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 955 = true := by
  have hs : count954 q = (countLit q [-95, -98, -100]) + (countLit q [-101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -100]) (l₂ := [-101, -103, -106, -108])
  have hm := merge_left (literal (valuationOf q) (944)) (literal (valuationOf q) (955)) (countLit q [-95, -98, -100]) (countLit q [-101, -103, -106, -108]) (count954 q) 2 (meaning944 q) (meaning955 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 955 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 950 = false ∨ valuationOf q 956 = true := by
  have hs : count954 q = (countLit q [-95, -98, -100]) + (countLit q [-101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -100]) (l₂ := [-101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (950)) (literal (valuationOf q) (956)) (countLit q [-95, -98, -100]) (countLit q [-101, -103, -106, -108]) (count954 q) 2 1 (meaning944 q) (meaning950 q) (meaning956 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 950 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 950 = false ∨ valuation q 956 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 955 = false ∨ valuationOf q 963 = true := by
  have hs : count961 q = (countLit q [-81, -85, -86, -88, -90, -92, -93]) + (countLit q [-95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86, -88, -90, -92, -93]) (l₂ := [-95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (955)) (literal (valuationOf q) (963)) (countLit q [-81, -85, -86, -88, -90, -92, -93]) (countLit q [-95, -98, -100, -101, -103, -106, -108]) (count961 q) 1 2 (meaning934 q) (meaning955 q) (meaning963 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 955 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 955 = false ∨ valuation q 963 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 956 = false ∨ valuationOf q 964 = true := by
  have hs : count961 q = (countLit q [-81, -85, -86, -88, -90, -92, -93]) + (countLit q [-95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86, -88, -90, -92, -93]) (l₂ := [-95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (956)) (literal (valuationOf q) (964)) (countLit q [-81, -85, -86, -88, -90, -92, -93]) (countLit q [-95, -98, -100, -101, -103, -106, -108]) (count961 q) 1 3 (meaning934 q) (meaning956 q) (meaning964 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 956 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 956 = false ∨ valuation q 964 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 954 = false ∨ valuationOf q 963 = true := by
  have hs : count961 q = (countLit q [-81, -85, -86, -88, -90, -92, -93]) + (countLit q [-95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86, -88, -90, -92, -93]) (l₂ := [-95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (954)) (literal (valuationOf q) (963)) (countLit q [-81, -85, -86, -88, -90, -92, -93]) (countLit q [-95, -98, -100, -101, -103, -106, -108]) (count961 q) 2 1 (meaning935 q) (meaning954 q) (meaning963 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 954 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 954 = false ∨ valuation q 963 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 955 = false ∨ valuationOf q 964 = true := by
  have hs : count961 q = (countLit q [-81, -85, -86, -88, -90, -92, -93]) + (countLit q [-95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86, -88, -90, -92, -93]) (l₂ := [-95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (955)) (literal (valuationOf q) (964)) (countLit q [-81, -85, -86, -88, -90, -92, -93]) (countLit q [-95, -98, -100, -101, -103, -106, -108]) (count961 q) 2 2 (meaning935 q) (meaning955 q) (meaning964 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 955 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 955 = false ∨ valuation q 964 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 956 = false ∨ valuationOf q 965 = true := by
  have hs : count961 q = (countLit q [-81, -85, -86, -88, -90, -92, -93]) + (countLit q [-95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86, -88, -90, -92, -93]) (l₂ := [-95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (956)) (literal (valuationOf q) (965)) (countLit q [-81, -85, -86, -88, -90, -92, -93]) (countLit q [-95, -98, -100, -101, -103, -106, -108]) (count961 q) 2 3 (meaning935 q) (meaning956 q) (meaning965 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 956 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 956 = false ∨ valuation q 965 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 963 = true := by
  have hs : count961 q = (countLit q [-81, -85, -86, -88, -90, -92, -93]) + (countLit q [-95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86, -88, -90, -92, -93]) (l₂ := [-95, -98, -100, -101, -103, -106, -108])
  have hm := merge_left (literal (valuationOf q) (936)) (literal (valuationOf q) (963)) (countLit q [-81, -85, -86, -88, -90, -92, -93]) (countLit q [-95, -98, -100, -101, -103, -106, -108]) (count961 q) 3 (meaning936 q) (meaning963 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 963 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 954 = false ∨ valuationOf q 964 = true := by
  have hs : count961 q = (countLit q [-81, -85, -86, -88, -90, -92, -93]) + (countLit q [-95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86, -88, -90, -92, -93]) (l₂ := [-95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (954)) (literal (valuationOf q) (964)) (countLit q [-81, -85, -86, -88, -90, -92, -93]) (countLit q [-95, -98, -100, -101, -103, -106, -108]) (count961 q) 3 1 (meaning936 q) (meaning954 q) (meaning964 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 954 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 954 = false ∨ valuation q 964 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 955 = false ∨ valuationOf q 965 = true := by
  have hs : count961 q = (countLit q [-81, -85, -86, -88, -90, -92, -93]) + (countLit q [-95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86, -88, -90, -92, -93]) (l₂ := [-95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (955)) (literal (valuationOf q) (965)) (countLit q [-81, -85, -86, -88, -90, -92, -93]) (countLit q [-95, -98, -100, -101, -103, -106, -108]) (count961 q) 3 2 (meaning936 q) (meaning955 q) (meaning965 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 955 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 955 = false ∨ valuation q 965 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 964 = true := by
  have hs : count961 q = (countLit q [-81, -85, -86, -88, -90, -92, -93]) + (countLit q [-95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86, -88, -90, -92, -93]) (l₂ := [-95, -98, -100, -101, -103, -106, -108])
  have hm := merge_left (literal (valuationOf q) (937)) (literal (valuationOf q) (964)) (countLit q [-81, -85, -86, -88, -90, -92, -93]) (countLit q [-95, -98, -100, -101, -103, -106, -108]) (count961 q) 4 (meaning937 q) (meaning964 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 964 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 954 = false ∨ valuationOf q 965 = true := by
  have hs : count961 q = (countLit q [-81, -85, -86, -88, -90, -92, -93]) + (countLit q [-95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86, -88, -90, -92, -93]) (l₂ := [-95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (937)) (literal (valuationOf q) (954)) (literal (valuationOf q) (965)) (countLit q [-81, -85, -86, -88, -90, -92, -93]) (countLit q [-95, -98, -100, -101, -103, -106, -108]) (count961 q) 4 1 (meaning937 q) (meaning954 q) (meaning965 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 954 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 954 = false ∨ valuation q 965 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 963 = false ∨ valuationOf q 978 = true := by
  have hs : count975 q = (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) + (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (l₂ := [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (963)) (literal (valuationOf q) (978)) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count975 q) 1 3 (meaning907 q) (meaning963 q) (meaning978 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 963 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 963 = false ∨ valuation q 978 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 963 = false ∨ valuationOf q 979 = true := by
  have hs : count975 q = (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) + (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (l₂ := [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (963)) (literal (valuationOf q) (979)) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count975 q) 2 3 (meaning908 q) (meaning963 q) (meaning979 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 963 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 963 = false ∨ valuation q 979 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 964 = false ∨ valuationOf q 980 = true := by
  have hs : count975 q = (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) + (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (l₂ := [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (964)) (literal (valuationOf q) (980)) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count975 q) 2 4 (meaning908 q) (meaning964 q) (meaning980 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 964 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 964 = false ∨ valuation q 980 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 965 = false ∨ valuationOf q 981 = true := by
  have hs : count975 q = (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) + (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (l₂ := [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (965)) (literal (valuationOf q) (981)) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count975 q) 2 5 (meaning908 q) (meaning965 q) (meaning981 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 965 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 965 = false ∨ valuation q 981 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 963 = false ∨ valuationOf q 980 = true := by
  have hs : count975 q = (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) + (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (l₂ := [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (963)) (literal (valuationOf q) (980)) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count975 q) 3 3 (meaning909 q) (meaning963 q) (meaning980 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 963 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 963 = false ∨ valuation q 980 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 964 = false ∨ valuationOf q 981 = true := by
  have hs : count975 q = (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) + (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (l₂ := [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (964)) (literal (valuationOf q) (981)) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count975 q) 3 4 (meaning909 q) (meaning964 q) (meaning981 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 964 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 964 = false ∨ valuation q 981 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 963 = false ∨ valuationOf q 981 = true := by
  have hs : count975 q = (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) + (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (l₂ := [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (963)) (literal (valuationOf q) (981)) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count975 q) 4 3 (meaning910 q) (meaning963 q) (meaning981 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 963 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 963 = false ∨ valuation q 981 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 964 = false ∨ valuationOf q 982 = true := by
  have hs : count975 q = (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) + (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (l₂ := [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (964)) (literal (valuationOf q) (982)) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count975 q) 4 4 (meaning910 q) (meaning964 q) (meaning982 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 964 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 964 = false ∨ valuation q 982 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 963 = false ∨ valuationOf q 982 = true := by
  have hs : count975 q = (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) + (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (l₂ := [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (963)) (literal (valuationOf q) (982)) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count975 q) 5 3 (meaning911 q) (meaning963 q) (meaning982 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 963 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 963 = false ∨ valuation q 982 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 963 = false ∨ valuationOf q 983 = true := by
  have hs : count975 q = (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) + (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (l₂ := [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (963)) (literal (valuationOf q) (983)) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]) (countLit q [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count975 q) 6 3 (meaning912 q) (meaning963 q) (meaning983 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 963 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 963 = false ∨ valuation q 983 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E185.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112185
