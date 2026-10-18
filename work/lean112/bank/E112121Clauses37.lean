import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 906 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_left (literal (valuationOf q) (894)) (literal (valuationOf q) (906)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 4 (meaning894 q) (meaning906 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 906 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 899 = false ∨ valuationOf q 907 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (899)) (literal (valuationOf q) (907)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 4 1 (meaning894 q) (meaning899 q) (meaning907 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 899 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 899 = false ∨ valuation q 907 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 900 = false ∨ valuationOf q 908 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (900)) (literal (valuationOf q) (908)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 4 2 (meaning894 q) (meaning900 q) (meaning908 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 900 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 900 = false ∨ valuation q 908 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 901 = false ∨ valuationOf q 909 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (901)) (literal (valuationOf q) (909)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 4 3 (meaning894 q) (meaning901 q) (meaning909 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 901 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 901 = false ∨ valuation q 909 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 905 = false ∨ valuationOf q 914 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (905)) (literal (valuationOf q) (914)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 1 3 (meaning879 q) (meaning905 q) (meaning914 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 905 = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 905 = false ∨ valuation q 914 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 906 = false ∨ valuationOf q 915 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (906)) (literal (valuationOf q) (915)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 1 4 (meaning879 q) (meaning906 q) (meaning915 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 906 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 906 = false ∨ valuation q 915 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 907 = false ∨ valuationOf q 916 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (907)) (literal (valuationOf q) (916)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 1 5 (meaning879 q) (meaning907 q) (meaning916 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 907 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 907 = false ∨ valuation q 916 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 908 = false ∨ valuationOf q 917 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (908)) (literal (valuationOf q) (917)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 1 6 (meaning879 q) (meaning908 q) (meaning917 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 908 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 908 = false ∨ valuation q 917 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 909 = false ∨ valuationOf q 918 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (909)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 1 7 (meaning879 q) (meaning909 q) (meaning918 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 909 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 909 = false ∨ valuation q 918 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 904 = false ∨ valuationOf q 914 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (904)) (literal (valuationOf q) (914)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 2 2 (meaning880 q) (meaning904 q) (meaning914 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 904 = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 904 = false ∨ valuation q 914 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 905 = false ∨ valuationOf q 915 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (905)) (literal (valuationOf q) (915)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 2 3 (meaning880 q) (meaning905 q) (meaning915 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 905 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 905 = false ∨ valuation q 915 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 906 = false ∨ valuationOf q 916 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (906)) (literal (valuationOf q) (916)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 2 4 (meaning880 q) (meaning906 q) (meaning916 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 906 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 906 = false ∨ valuation q 916 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 907 = false ∨ valuationOf q 917 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (907)) (literal (valuationOf q) (917)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 2 5 (meaning880 q) (meaning907 q) (meaning917 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 907 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 907 = false ∨ valuation q 917 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 908 = false ∨ valuationOf q 918 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (908)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 2 6 (meaning880 q) (meaning908 q) (meaning918 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 908 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 908 = false ∨ valuation q 918 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 909 = false ∨ valuationOf q 919 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (909)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 2 7 (meaning880 q) (meaning909 q) (meaning919 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 909 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 909 = false ∨ valuation q 919 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 903 = false ∨ valuationOf q 914 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (903)) (literal (valuationOf q) (914)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 3 1 (meaning881 q) (meaning903 q) (meaning914 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 903 = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 903 = false ∨ valuation q 914 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 904 = false ∨ valuationOf q 915 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (904)) (literal (valuationOf q) (915)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 3 2 (meaning881 q) (meaning904 q) (meaning915 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 904 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 904 = false ∨ valuation q 915 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 905 = false ∨ valuationOf q 916 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (905)) (literal (valuationOf q) (916)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 3 3 (meaning881 q) (meaning905 q) (meaning916 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 905 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 905 = false ∨ valuation q 916 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 906 = false ∨ valuationOf q 917 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (906)) (literal (valuationOf q) (917)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 3 4 (meaning881 q) (meaning906 q) (meaning917 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 906 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 906 = false ∨ valuation q 917 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 907 = false ∨ valuationOf q 918 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (907)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 3 5 (meaning881 q) (meaning907 q) (meaning918 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 907 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 907 = false ∨ valuation q 918 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 908 = false ∨ valuationOf q 919 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (908)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 3 6 (meaning881 q) (meaning908 q) (meaning919 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 908 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 908 = false ∨ valuation q 919 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 914 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_left (literal (valuationOf q) (882)) (literal (valuationOf q) (914)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 4 (meaning882 q) (meaning914 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 914 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 903 = false ∨ valuationOf q 915 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (903)) (literal (valuationOf q) (915)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 4 1 (meaning882 q) (meaning903 q) (meaning915 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 903 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 903 = false ∨ valuation q 915 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 904 = false ∨ valuationOf q 916 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (904)) (literal (valuationOf q) (916)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 4 2 (meaning882 q) (meaning904 q) (meaning916 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 904 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 904 = false ∨ valuation q 916 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 905 = false ∨ valuationOf q 917 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (905)) (literal (valuationOf q) (917)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 4 3 (meaning882 q) (meaning905 q) (meaning917 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 905 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 905 = false ∨ valuation q 917 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 906 = false ∨ valuationOf q 918 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (906)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 4 4 (meaning882 q) (meaning906 q) (meaning918 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 906 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 906 = false ∨ valuation q 918 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 907 = false ∨ valuationOf q 919 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (907)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 4 5 (meaning882 q) (meaning907 q) (meaning919 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 907 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 907 = false ∨ valuation q 919 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 908 = false ∨ valuationOf q 920 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (908)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 4 6 (meaning882 q) (meaning908 q) (meaning920 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 908 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 908 = false ∨ valuation q 920 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 909 = false ∨ valuationOf q 921 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (909)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 4 7 (meaning882 q) (meaning909 q) (meaning921 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 909 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 909 = false ∨ valuation q 921 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 915 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_left (literal (valuationOf q) (883)) (literal (valuationOf q) (915)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 5 (meaning883 q) (meaning915 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 915 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 903 = false ∨ valuationOf q 916 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (903)) (literal (valuationOf q) (916)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 5 1 (meaning883 q) (meaning903 q) (meaning916 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 903 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 903 = false ∨ valuation q 916 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 904 = false ∨ valuationOf q 917 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (904)) (literal (valuationOf q) (917)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 5 2 (meaning883 q) (meaning904 q) (meaning917 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 904 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 904 = false ∨ valuation q 917 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E121.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112121
