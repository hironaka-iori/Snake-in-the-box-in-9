import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 879 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_right (literal (valuationOf q) (875)) (literal (valuationOf q) (879)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 3 (meaning875 q) (meaning879 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 879 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 880 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_right (literal (valuationOf q) (876)) (literal (valuationOf q) (880)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 4 (meaning876 q) (meaning880 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 880 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 877 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_left (literal (valuationOf q) (865)) (literal (valuationOf q) (877)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 1 (meaning865 q) (meaning877 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 877 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 873 = false ∨ valuationOf q 878 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (873)) (literal (valuationOf q) (878)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 1 1 (meaning865 q) (meaning873 q) (meaning878 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 873 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 873 = false ∨ valuation q 878 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 874 = false ∨ valuationOf q 879 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (874)) (literal (valuationOf q) (879)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 1 2 (meaning865 q) (meaning874 q) (meaning879 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 874 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 874 = false ∨ valuation q 879 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 875 = false ∨ valuationOf q 880 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (875)) (literal (valuationOf q) (880)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 1 3 (meaning865 q) (meaning875 q) (meaning880 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 875 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 875 = false ∨ valuation q 880 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 876 = false ∨ valuationOf q 881 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (876)) (literal (valuationOf q) (881)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 1 4 (meaning865 q) (meaning876 q) (meaning881 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 876 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 876 = false ∨ valuation q 881 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 878 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_left (literal (valuationOf q) (866)) (literal (valuationOf q) (878)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 2 (meaning866 q) (meaning878 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 878 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 873 = false ∨ valuationOf q 879 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (873)) (literal (valuationOf q) (879)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 2 1 (meaning866 q) (meaning873 q) (meaning879 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 873 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 873 = false ∨ valuation q 879 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 874 = false ∨ valuationOf q 880 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (874)) (literal (valuationOf q) (880)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 2 2 (meaning866 q) (meaning874 q) (meaning880 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 874 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 874 = false ∨ valuation q 880 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 875 = false ∨ valuationOf q 881 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (875)) (literal (valuationOf q) (881)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 2 3 (meaning866 q) (meaning875 q) (meaning881 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 875 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 875 = false ∨ valuation q 881 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 876 = false ∨ valuationOf q 882 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (876)) (literal (valuationOf q) (882)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 2 4 (meaning866 q) (meaning876 q) (meaning882 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 876 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 876 = false ∨ valuation q 882 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 879 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_left (literal (valuationOf q) (867)) (literal (valuationOf q) (879)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 3 (meaning867 q) (meaning879 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 879 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 873 = false ∨ valuationOf q 880 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (873)) (literal (valuationOf q) (880)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 3 1 (meaning867 q) (meaning873 q) (meaning880 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 873 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 873 = false ∨ valuation q 880 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 874 = false ∨ valuationOf q 881 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (874)) (literal (valuationOf q) (881)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 3 2 (meaning867 q) (meaning874 q) (meaning881 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 874 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 874 = false ∨ valuation q 881 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 875 = false ∨ valuationOf q 882 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (875)) (literal (valuationOf q) (882)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 3 3 (meaning867 q) (meaning875 q) (meaning882 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 875 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 875 = false ∨ valuation q 882 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 880 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_left (literal (valuationOf q) (868)) (literal (valuationOf q) (880)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 4 (meaning868 q) (meaning880 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 880 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 873 = false ∨ valuationOf q 881 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (873)) (literal (valuationOf q) (881)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 4 1 (meaning868 q) (meaning873 q) (meaning881 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 873 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 873 = false ∨ valuation q 881 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 874 = false ∨ valuationOf q 882 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (874)) (literal (valuationOf q) (882)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 4 2 (meaning868 q) (meaning874 q) (meaning882 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 874 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 874 = false ∨ valuation q 882 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 885 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_right (literal (valuationOf q) (877)) (literal (valuationOf q) (885)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 1 (meaning877 q) (meaning885 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 885 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_right (literal (valuationOf q) (878)) (literal (valuationOf q) (886)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 2 (meaning878 q) (meaning886 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 886 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_right (literal (valuationOf q) (879)) (literal (valuationOf q) (887)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 3 (meaning879 q) (meaning887 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 887 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_right (literal (valuationOf q) (880)) (literal (valuationOf q) (888)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 4 (meaning880 q) (meaning888 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 888 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_right (literal (valuationOf q) (881)) (literal (valuationOf q) (889)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 5 (meaning881 q) (meaning889 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 889 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_right (literal (valuationOf q) (882)) (literal (valuationOf q) (890)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 6 (meaning882 q) (meaning890 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 890 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 885 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_left (literal (valuationOf q) (854)) (literal (valuationOf q) (885)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 1 (meaning854 q) (meaning885 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 885 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 877 = false ∨ valuationOf q 886 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (877)) (literal (valuationOf q) (886)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 1 1 (meaning854 q) (meaning877 q) (meaning886 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 877 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 877 = false ∨ valuation q 886 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 878 = false ∨ valuationOf q 887 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (878)) (literal (valuationOf q) (887)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 1 2 (meaning854 q) (meaning878 q) (meaning887 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 878 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 878 = false ∨ valuation q 887 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 879 = false ∨ valuationOf q 888 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (879)) (literal (valuationOf q) (888)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 1 3 (meaning854 q) (meaning879 q) (meaning888 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 879 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 879 = false ∨ valuation q 888 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 880 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (880)) (literal (valuationOf q) (889)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 1 4 (meaning854 q) (meaning880 q) (meaning889 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 880 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 880 = false ∨ valuation q 889 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 881 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (881)) (literal (valuationOf q) (890)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 1 5 (meaning854 q) (meaning881 q) (meaning890 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 881 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 881 = false ∨ valuation q 890 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 882 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-30, -32, -34, -40, -42, -44, -45]) + (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -40, -42, -44, -45]) (l₂ := [-46, -48, -49, -50, -52, -54, -59, -60])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (882)) (literal (valuationOf q) (891)) (countLit q [-30, -32, -34, -40, -42, -44, -45]) (countLit q [-46, -48, -49, -50, -52, -54, -59, -60]) (count885 q) 1 6 (meaning854 q) (meaning882 q) (meaning891 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 882 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 882 = false ∨ valuation q 891 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E257.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112257
