import Glue1
/-! Glue, part 2: a largest 6-subcube, moved to copy 0 of coordinates (6,7) by a stored word. -/
set_option linter.deprecated false
set_option maxRecDepth 200000
namespace Dim8Lift.Sym
open Dim8Lift Dim8Lift.Cube

/-- for each subcube (a < b, va, vb): a word g with (u < 64) ↔ g u in the subcube -/
def moves : List ((Nat × Nat × Bool × Bool) × List Nat) := [
  ((0, 1, false, false), [5, 12]),
  ((0, 1, false, true), [5, 12, 35]),
  ((0, 1, true, false), [5, 12, 34]),
  ((0, 1, true, true), [5, 12, 34, 35]),
  ((0, 2, false, false), [5, 17]),
  ((0, 2, false, true), [5, 17, 35]),
  ((0, 2, true, false), [5, 17, 34]),
  ((0, 2, true, true), [5, 17, 34, 35]),
  ((0, 3, false, false), [5, 21]),
  ((0, 3, false, true), [5, 21, 35]),
  ((0, 3, true, false), [5, 21, 34]),
  ((0, 3, true, true), [5, 21, 34, 35]),
  ((0, 4, false, false), [5, 24]),
  ((0, 4, false, true), [5, 24, 35]),
  ((0, 4, true, false), [5, 24, 34]),
  ((0, 4, true, true), [5, 24, 34, 35]),
  ((0, 5, false, false), [5, 26]),
  ((0, 5, false, true), [5, 26, 35]),
  ((0, 5, true, false), [5, 26, 34]),
  ((0, 5, true, true), [5, 26, 34, 35]),
  ((0, 6, false, false), [6]),
  ((0, 6, false, true), [6, 34]),
  ((0, 6, true, false), [6, 35]),
  ((0, 6, true, true), [6, 34, 35]),
  ((0, 7, false, false), [5]),
  ((0, 7, false, true), [5, 35]),
  ((0, 7, true, false), [5, 34]),
  ((0, 7, true, true), [5, 34, 35]),
  ((1, 2, false, false), [11, 17]),
  ((1, 2, false, true), [11, 17, 35]),
  ((1, 2, true, false), [11, 17, 34]),
  ((1, 2, true, true), [11, 17, 34, 35]),
  ((1, 3, false, false), [11, 21]),
  ((1, 3, false, true), [11, 21, 35]),
  ((1, 3, true, false), [11, 21, 34]),
  ((1, 3, true, true), [11, 21, 34, 35]),
  ((1, 4, false, false), [11, 24]),
  ((1, 4, false, true), [11, 24, 35]),
  ((1, 4, true, false), [11, 24, 34]),
  ((1, 4, true, true), [11, 24, 34, 35]),
  ((1, 5, false, false), [11, 26]),
  ((1, 5, false, true), [11, 26, 35]),
  ((1, 5, true, false), [11, 26, 34]),
  ((1, 5, true, true), [11, 26, 34, 35]),
  ((1, 6, false, false), [12]),
  ((1, 6, false, true), [12, 34]),
  ((1, 6, true, false), [12, 35]),
  ((1, 6, true, true), [12, 34, 35]),
  ((1, 7, false, false), [11]),
  ((1, 7, false, true), [11, 35]),
  ((1, 7, true, false), [11, 34]),
  ((1, 7, true, true), [11, 34, 35]),
  ((2, 3, false, false), [16, 21]),
  ((2, 3, false, true), [16, 21, 35]),
  ((2, 3, true, false), [16, 21, 34]),
  ((2, 3, true, true), [16, 21, 34, 35]),
  ((2, 4, false, false), [16, 24]),
  ((2, 4, false, true), [16, 24, 35]),
  ((2, 4, true, false), [16, 24, 34]),
  ((2, 4, true, true), [16, 24, 34, 35]),
  ((2, 5, false, false), [16, 26]),
  ((2, 5, false, true), [16, 26, 35]),
  ((2, 5, true, false), [16, 26, 34]),
  ((2, 5, true, true), [16, 26, 34, 35]),
  ((2, 6, false, false), [17]),
  ((2, 6, false, true), [17, 34]),
  ((2, 6, true, false), [17, 35]),
  ((2, 6, true, true), [17, 34, 35]),
  ((2, 7, false, false), [16]),
  ((2, 7, false, true), [16, 35]),
  ((2, 7, true, false), [16, 34]),
  ((2, 7, true, true), [16, 34, 35]),
  ((3, 4, false, false), [20, 24]),
  ((3, 4, false, true), [20, 24, 35]),
  ((3, 4, true, false), [20, 24, 34]),
  ((3, 4, true, true), [20, 24, 34, 35]),
  ((3, 5, false, false), [20, 26]),
  ((3, 5, false, true), [20, 26, 35]),
  ((3, 5, true, false), [20, 26, 34]),
  ((3, 5, true, true), [20, 26, 34, 35]),
  ((3, 6, false, false), [21]),
  ((3, 6, false, true), [21, 34]),
  ((3, 6, true, false), [21, 35]),
  ((3, 6, true, true), [21, 34, 35]),
  ((3, 7, false, false), [20]),
  ((3, 7, false, true), [20, 35]),
  ((3, 7, true, false), [20, 34]),
  ((3, 7, true, true), [20, 34, 35]),
  ((4, 5, false, false), [23, 26]),
  ((4, 5, false, true), [23, 26, 35]),
  ((4, 5, true, false), [23, 26, 34]),
  ((4, 5, true, true), [23, 26, 34, 35]),
  ((4, 6, false, false), [24]),
  ((4, 6, false, true), [24, 34]),
  ((4, 6, true, false), [24, 35]),
  ((4, 6, true, true), [24, 34, 35]),
  ((4, 7, false, false), [23]),
  ((4, 7, false, true), [23, 35]),
  ((4, 7, true, false), [23, 34]),
  ((4, 7, true, true), [23, 34, 35]),
  ((5, 6, false, false), [26]),
  ((5, 6, false, true), [26, 34]),
  ((5, 6, true, false), [26, 35]),
  ((5, 6, true, true), [26, 34, 35]),
  ((5, 7, false, false), [25]),
  ((5, 7, false, true), [25, 35]),
  ((5, 7, true, false), [25, 34]),
  ((5, 7, true, true), [25, 34, 35]),
  ((6, 7, false, false), []),
  ((6, 7, false, true), [35]),
  ((6, 7, true, false), [34]),
  ((6, 7, true, true), [34, 35])]

def MoveOK (e : (Nat × Nat × Bool × Bool) × List Nat) : Prop :=
  (e.2.all (· < 36) = true) ∧ ∀ u : Fin 256, decide (u.val < 64) = inSub e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 (applyW e.2 u.val)

theorem move_0 : MoveOK (moves.getD 0 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_1 : MoveOK (moves.getD 1 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_2 : MoveOK (moves.getD 2 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_3 : MoveOK (moves.getD 3 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_4 : MoveOK (moves.getD 4 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_5 : MoveOK (moves.getD 5 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_6 : MoveOK (moves.getD 6 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_7 : MoveOK (moves.getD 7 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_8 : MoveOK (moves.getD 8 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_9 : MoveOK (moves.getD 9 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_10 : MoveOK (moves.getD 10 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_11 : MoveOK (moves.getD 11 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_12 : MoveOK (moves.getD 12 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_13 : MoveOK (moves.getD 13 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_14 : MoveOK (moves.getD 14 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_15 : MoveOK (moves.getD 15 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_16 : MoveOK (moves.getD 16 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_17 : MoveOK (moves.getD 17 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_18 : MoveOK (moves.getD 18 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_19 : MoveOK (moves.getD 19 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_20 : MoveOK (moves.getD 20 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_21 : MoveOK (moves.getD 21 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_22 : MoveOK (moves.getD 22 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_23 : MoveOK (moves.getD 23 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_24 : MoveOK (moves.getD 24 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_25 : MoveOK (moves.getD 25 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_26 : MoveOK (moves.getD 26 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_27 : MoveOK (moves.getD 27 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_28 : MoveOK (moves.getD 28 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_29 : MoveOK (moves.getD 29 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_30 : MoveOK (moves.getD 30 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_31 : MoveOK (moves.getD 31 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_32 : MoveOK (moves.getD 32 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_33 : MoveOK (moves.getD 33 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_34 : MoveOK (moves.getD 34 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_35 : MoveOK (moves.getD 35 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_36 : MoveOK (moves.getD 36 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_37 : MoveOK (moves.getD 37 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_38 : MoveOK (moves.getD 38 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_39 : MoveOK (moves.getD 39 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_40 : MoveOK (moves.getD 40 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_41 : MoveOK (moves.getD 41 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_42 : MoveOK (moves.getD 42 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_43 : MoveOK (moves.getD 43 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_44 : MoveOK (moves.getD 44 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_45 : MoveOK (moves.getD 45 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_46 : MoveOK (moves.getD 46 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_47 : MoveOK (moves.getD 47 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_48 : MoveOK (moves.getD 48 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_49 : MoveOK (moves.getD 49 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_50 : MoveOK (moves.getD 50 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_51 : MoveOK (moves.getD 51 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_52 : MoveOK (moves.getD 52 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_53 : MoveOK (moves.getD 53 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_54 : MoveOK (moves.getD 54 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_55 : MoveOK (moves.getD 55 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_56 : MoveOK (moves.getD 56 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_57 : MoveOK (moves.getD 57 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_58 : MoveOK (moves.getD 58 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_59 : MoveOK (moves.getD 59 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_60 : MoveOK (moves.getD 60 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_61 : MoveOK (moves.getD 61 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_62 : MoveOK (moves.getD 62 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_63 : MoveOK (moves.getD 63 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_64 : MoveOK (moves.getD 64 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_65 : MoveOK (moves.getD 65 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_66 : MoveOK (moves.getD 66 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_67 : MoveOK (moves.getD 67 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_68 : MoveOK (moves.getD 68 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_69 : MoveOK (moves.getD 69 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_70 : MoveOK (moves.getD 70 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_71 : MoveOK (moves.getD 71 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_72 : MoveOK (moves.getD 72 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_73 : MoveOK (moves.getD 73 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_74 : MoveOK (moves.getD 74 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_75 : MoveOK (moves.getD 75 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_76 : MoveOK (moves.getD 76 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_77 : MoveOK (moves.getD 77 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_78 : MoveOK (moves.getD 78 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_79 : MoveOK (moves.getD 79 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_80 : MoveOK (moves.getD 80 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_81 : MoveOK (moves.getD 81 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_82 : MoveOK (moves.getD 82 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_83 : MoveOK (moves.getD 83 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_84 : MoveOK (moves.getD 84 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_85 : MoveOK (moves.getD 85 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_86 : MoveOK (moves.getD 86 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_87 : MoveOK (moves.getD 87 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_88 : MoveOK (moves.getD 88 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_89 : MoveOK (moves.getD 89 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_90 : MoveOK (moves.getD 90 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_91 : MoveOK (moves.getD 91 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_92 : MoveOK (moves.getD 92 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_93 : MoveOK (moves.getD 93 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_94 : MoveOK (moves.getD 94 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_95 : MoveOK (moves.getD 95 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_96 : MoveOK (moves.getD 96 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_97 : MoveOK (moves.getD 97 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_98 : MoveOK (moves.getD 98 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_99 : MoveOK (moves.getD 99 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_100 : MoveOK (moves.getD 100 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_101 : MoveOK (moves.getD 101 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_102 : MoveOK (moves.getD 102 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_103 : MoveOK (moves.getD 103 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_104 : MoveOK (moves.getD 104 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_105 : MoveOK (moves.getD 105 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_106 : MoveOK (moves.getD 106 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_107 : MoveOK (moves.getD 107 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_108 : MoveOK (moves.getD 108 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_109 : MoveOK (moves.getD 109 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_110 : MoveOK (moves.getD 110 ((0, 0, false, false), [])) := by unfold MoveOK; decide
theorem move_111 : MoveOK (moves.getD 111 ((0, 0, false, false), [])) := by unfold MoveOK; decide

theorem moves_len : moves.length = 112 := rfl

theorem move_idx : ∀ i, i < 112 → MoveOK (moves.getD i ((0, 0, false, false), []))
  | 0, _ => move_0
  | 1, _ => move_1
  | 2, _ => move_2
  | 3, _ => move_3
  | 4, _ => move_4
  | 5, _ => move_5
  | 6, _ => move_6
  | 7, _ => move_7
  | 8, _ => move_8
  | 9, _ => move_9
  | 10, _ => move_10
  | 11, _ => move_11
  | 12, _ => move_12
  | 13, _ => move_13
  | 14, _ => move_14
  | 15, _ => move_15
  | 16, _ => move_16
  | 17, _ => move_17
  | 18, _ => move_18
  | 19, _ => move_19
  | 20, _ => move_20
  | 21, _ => move_21
  | 22, _ => move_22
  | 23, _ => move_23
  | 24, _ => move_24
  | 25, _ => move_25
  | 26, _ => move_26
  | 27, _ => move_27
  | 28, _ => move_28
  | 29, _ => move_29
  | 30, _ => move_30
  | 31, _ => move_31
  | 32, _ => move_32
  | 33, _ => move_33
  | 34, _ => move_34
  | 35, _ => move_35
  | 36, _ => move_36
  | 37, _ => move_37
  | 38, _ => move_38
  | 39, _ => move_39
  | 40, _ => move_40
  | 41, _ => move_41
  | 42, _ => move_42
  | 43, _ => move_43
  | 44, _ => move_44
  | 45, _ => move_45
  | 46, _ => move_46
  | 47, _ => move_47
  | 48, _ => move_48
  | 49, _ => move_49
  | 50, _ => move_50
  | 51, _ => move_51
  | 52, _ => move_52
  | 53, _ => move_53
  | 54, _ => move_54
  | 55, _ => move_55
  | 56, _ => move_56
  | 57, _ => move_57
  | 58, _ => move_58
  | 59, _ => move_59
  | 60, _ => move_60
  | 61, _ => move_61
  | 62, _ => move_62
  | 63, _ => move_63
  | 64, _ => move_64
  | 65, _ => move_65
  | 66, _ => move_66
  | 67, _ => move_67
  | 68, _ => move_68
  | 69, _ => move_69
  | 70, _ => move_70
  | 71, _ => move_71
  | 72, _ => move_72
  | 73, _ => move_73
  | 74, _ => move_74
  | 75, _ => move_75
  | 76, _ => move_76
  | 77, _ => move_77
  | 78, _ => move_78
  | 79, _ => move_79
  | 80, _ => move_80
  | 81, _ => move_81
  | 82, _ => move_82
  | 83, _ => move_83
  | 84, _ => move_84
  | 85, _ => move_85
  | 86, _ => move_86
  | 87, _ => move_87
  | 88, _ => move_88
  | 89, _ => move_89
  | 90, _ => move_90
  | 91, _ => move_91
  | 92, _ => move_92
  | 93, _ => move_93
  | 94, _ => move_94
  | 95, _ => move_95
  | 96, _ => move_96
  | 97, _ => move_97
  | 98, _ => move_98
  | 99, _ => move_99
  | 100, _ => move_100
  | 101, _ => move_101
  | 102, _ => move_102
  | 103, _ => move_103
  | 104, _ => move_104
  | 105, _ => move_105
  | 106, _ => move_106
  | 107, _ => move_107
  | 108, _ => move_108
  | 109, _ => move_109
  | 110, _ => move_110
  | 111, _ => move_111
  | n + 112, h => absurd h (by omega)

theorem moves_ok : ∀ e ∈ moves, MoveOK e := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have := move_idx i (by rw [moves_len] at hi; exact hi)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at this
  simpa using this

end Dim8Lift.Sym
