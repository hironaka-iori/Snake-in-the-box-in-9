import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 912 = false ∨ valuationOf q 915 = true := by
  have hs : count914 q = (countLit q [-39, -43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-39, -43]) (l₂ := [-45, -46])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (912)) (literal (valuationOf q) (915)) (countLit q [-39, -43]) (countLit q [-45, -46]) (count914 q) 1 1 (meaning910 q) (meaning912 q) (meaning915 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 912 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 912 = false ∨ valuation q 915 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 913 = false ∨ valuationOf q 916 = true := by
  have hs : count914 q = (countLit q [-39, -43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-39, -43]) (l₂ := [-45, -46])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (913)) (literal (valuationOf q) (916)) (countLit q [-39, -43]) (countLit q [-45, -46]) (count914 q) 1 2 (meaning910 q) (meaning913 q) (meaning916 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 913 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 913 = false ∨ valuation q 916 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 915 = true := by
  have hs : count914 q = (countLit q [-39, -43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-39, -43]) (l₂ := [-45, -46])
  have hm := merge_left (literal (valuationOf q) (911)) (literal (valuationOf q) (915)) (countLit q [-39, -43]) (countLit q [-45, -46]) (count914 q) 2 (meaning911 q) (meaning915 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 915 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 912 = false ∨ valuationOf q 916 = true := by
  have hs : count914 q = (countLit q [-39, -43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-39, -43]) (l₂ := [-45, -46])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (912)) (literal (valuationOf q) (916)) (countLit q [-39, -43]) (countLit q [-45, -46]) (count914 q) 2 1 (meaning911 q) (meaning912 q) (meaning916 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 912 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 912 = false ∨ valuation q 916 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 918 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_right (literal (valuationOf q) (914)) (literal (valuationOf q) (918)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 1 (meaning914 q) (meaning918 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 918 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 915 = false ∨ valuationOf q 919 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_right (literal (valuationOf q) (915)) (literal (valuationOf q) (919)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 2 (meaning915 q) (meaning919 q) hs
  change valuationOf q 915 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 915 = false ∨ valuation q 919 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 920 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_right (literal (valuationOf q) (916)) (literal (valuationOf q) (920)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 3 (meaning916 q) (meaning920 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 920 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 918 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_left (literal (valuationOf q) (906)) (literal (valuationOf q) (918)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 1 (meaning906 q) (meaning918 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 918 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 914 = false ∨ valuationOf q 919 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (914)) (literal (valuationOf q) (919)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 1 1 (meaning906 q) (meaning914 q) (meaning919 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 914 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 914 = false ∨ valuation q 919 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 915 = false ∨ valuationOf q 920 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (915)) (literal (valuationOf q) (920)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 1 2 (meaning906 q) (meaning915 q) (meaning920 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 915 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 915 = false ∨ valuation q 920 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 916 = false ∨ valuationOf q 921 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (916)) (literal (valuationOf q) (921)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 1 3 (meaning906 q) (meaning916 q) (meaning921 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 916 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 916 = false ∨ valuation q 921 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 919 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_left (literal (valuationOf q) (907)) (literal (valuationOf q) (919)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 2 (meaning907 q) (meaning919 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 919 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 914 = false ∨ valuationOf q 920 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (914)) (literal (valuationOf q) (920)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 2 1 (meaning907 q) (meaning914 q) (meaning920 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 914 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 914 = false ∨ valuation q 920 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 915 = false ∨ valuationOf q 921 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (915)) (literal (valuationOf q) (921)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 2 2 (meaning907 q) (meaning915 q) (meaning921 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 915 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 915 = false ∨ valuation q 921 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 916 = false ∨ valuationOf q 922 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (916)) (literal (valuationOf q) (922)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 2 3 (meaning907 q) (meaning916 q) (meaning922 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 916 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 916 = false ∨ valuation q 922 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 920 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_left (literal (valuationOf q) (908)) (literal (valuationOf q) (920)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 3 (meaning908 q) (meaning920 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 920 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 914 = false ∨ valuationOf q 921 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (914)) (literal (valuationOf q) (921)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 3 1 (meaning908 q) (meaning914 q) (meaning921 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 914 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 914 = false ∨ valuation q 921 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 915 = false ∨ valuationOf q 922 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (915)) (literal (valuationOf q) (922)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 3 2 (meaning908 q) (meaning915 q) (meaning922 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 915 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 915 = false ∨ valuation q 922 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 921 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_left (literal (valuationOf q) (909)) (literal (valuationOf q) (921)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 4 (meaning909 q) (meaning921 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 921 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 914 = false ∨ valuationOf q 922 = true := by
  have hs : count918 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (914)) (literal (valuationOf q) (922)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -43, -45, -46]) (count918 q) 4 1 (meaning909 q) (meaning914 q) (meaning922 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 914 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 914 = false ∨ valuation q 922 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 926 = true := by
  have hs : count926 q = (countLit q [-47]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (926)) (countLit q [-47]) (countLit q [-51]) (count926 q) 1 (meaningNeg51 q) (meaning926 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 926 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 926 = true := by
  have hs : count926 q = (countLit q [-47]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (926)) (countLit q [-47]) (countLit q [-51]) (count926 q) 1 (meaningNeg47 q) (meaning926 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 926 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 51 = true ∨ valuationOf q 927 = true := by
  have hs : count926 q = (countLit q [-47]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (927)) (countLit q [-47]) (countLit q [-51]) (count926 q) 1 1 (meaningNeg47 q) (meaningNeg51 q) (meaning927 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 51 = true ∨ valuation q 927 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 928 = true := by
  have hs : count928 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (928)) (countLit q [-52]) (countLit q [-53]) (count928 q) 1 (meaningNeg53 q) (meaning928 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 928 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 928 = true := by
  have hs : count928 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (928)) (countLit q [-52]) (countLit q [-53]) (count928 q) 1 (meaningNeg52 q) (meaning928 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 928 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 53 = true ∨ valuationOf q 929 = true := by
  have hs : count928 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (929)) (countLit q [-52]) (countLit q [-53]) (count928 q) 1 1 (meaningNeg52 q) (meaningNeg53 q) (meaning929 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 929 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 930 = true := by
  have hs : count930 q = (countLit q [-47, -51]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-47, -51]) (l₂ := [-52, -53])
  have hm := merge_left (literal (valuationOf q) (926)) (literal (valuationOf q) (930)) (countLit q [-47, -51]) (countLit q [-52, -53]) (count930 q) 1 (meaning926 q) (meaning930 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 930 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 928 = false ∨ valuationOf q 931 = true := by
  have hs : count930 q = (countLit q [-47, -51]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-47, -51]) (l₂ := [-52, -53])
  have hm := merge_two (literal (valuationOf q) (926)) (literal (valuationOf q) (928)) (literal (valuationOf q) (931)) (countLit q [-47, -51]) (countLit q [-52, -53]) (count930 q) 1 1 (meaning926 q) (meaning928 q) (meaning931 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 928 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 928 = false ∨ valuation q 931 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 929 = false ∨ valuationOf q 932 = true := by
  have hs : count930 q = (countLit q [-47, -51]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-47, -51]) (l₂ := [-52, -53])
  have hm := merge_two (literal (valuationOf q) (926)) (literal (valuationOf q) (929)) (literal (valuationOf q) (932)) (countLit q [-47, -51]) (countLit q [-52, -53]) (count930 q) 1 2 (meaning926 q) (meaning929 q) (meaning932 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 929 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 929 = false ∨ valuation q 932 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 927 = false ∨ valuationOf q 931 = true := by
  have hs : count930 q = (countLit q [-47, -51]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-47, -51]) (l₂ := [-52, -53])
  have hm := merge_left (literal (valuationOf q) (927)) (literal (valuationOf q) (931)) (countLit q [-47, -51]) (countLit q [-52, -53]) (count930 q) 2 (meaning927 q) (meaning931 q) hs
  change valuationOf q 927 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 927 = false ∨ valuation q 931 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 927 = false ∨ valuationOf q 928 = false ∨ valuationOf q 932 = true := by
  have hs : count930 q = (countLit q [-47, -51]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-47, -51]) (l₂ := [-52, -53])
  have hm := merge_two (literal (valuationOf q) (927)) (literal (valuationOf q) (928)) (literal (valuationOf q) (932)) (countLit q [-47, -51]) (countLit q [-52, -53]) (count930 q) 2 1 (meaning927 q) (meaning928 q) (meaning932 q) hs
  change valuationOf q 927 = false ∨ valuationOf q 928 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 927 = false ∨ valuation q 928 = false ∨ valuation q 932 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 934 = true := by
  have hs : count934 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (934)) (countLit q [-55]) (countLit q [-57]) (count934 q) 1 (meaningNeg57 q) (meaning934 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 934 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E153.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112153
