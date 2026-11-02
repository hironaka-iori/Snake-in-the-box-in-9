import PotentialBlocks102

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.PotentialBlocks102
open Snake9.Potential99 Snake9.Balanced89

theorem completed_at_52 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (404352+offset) =
      min 551 (value Completed.n5_156 offset) := by
  have hr : lookup Completed.roots 52 (.leaf 0) = Completed.n5_156 := by rfl
  simpa only [hr] using completed_block 52 offset hoff

#print axioms completed_at_52

theorem conditional_at_52 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (404352+offset) =
      min 602 (value Conditional.n5_150 offset) := by
  have hr : lookup Conditional.roots 52 (.leaf 0) = Conditional.n5_150 := by rfl
  simpa only [hr] using conditional_block 52 offset hoff

#print axioms conditional_at_52

theorem completed_at_53 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (412128+offset) =
      min 551 (value Completed.n5_147 offset) := by
  have hr : lookup Completed.roots 53 (.leaf 0) = Completed.n5_147 := by rfl
  simpa only [hr] using completed_block 53 offset hoff

#print axioms completed_at_53

theorem conditional_at_53 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (412128+offset) =
      min 602 (value Conditional.n5_139 offset) := by
  have hr : lookup Conditional.roots 53 (.leaf 0) = Conditional.n5_139 := by rfl
  simpa only [hr] using conditional_block 53 offset hoff

#print axioms conditional_at_53

theorem completed_at_54 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (419904+offset) =
      min 551 (value Completed.n5_172 offset) := by
  have hr : lookup Completed.roots 54 (.leaf 0) = Completed.n5_172 := by rfl
  simpa only [hr] using completed_block 54 offset hoff

#print axioms completed_at_54

theorem conditional_at_54 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (419904+offset) =
      min 602 (value Conditional.n5_168 offset) := by
  have hr : lookup Conditional.roots 54 (.leaf 0) = Conditional.n5_168 := by rfl
  simpa only [hr] using conditional_block 54 offset hoff

#print axioms conditional_at_54

theorem completed_at_55 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (427680+offset) =
      min 551 (value Completed.n5_168 offset) := by
  have hr : lookup Completed.roots 55 (.leaf 0) = Completed.n5_168 := by rfl
  simpa only [hr] using completed_block 55 offset hoff

#print axioms completed_at_55

theorem conditional_at_55 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (427680+offset) =
      min 602 (value Conditional.n5_164 offset) := by
  have hr : lookup Conditional.roots 55 (.leaf 0) = Conditional.n5_164 := by rfl
  simpa only [hr] using conditional_block 55 offset hoff

#print axioms conditional_at_55

theorem completed_at_56 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (435456+offset) =
      min 551 (value Completed.n5_163 offset) := by
  have hr : lookup Completed.roots 56 (.leaf 0) = Completed.n5_163 := by rfl
  simpa only [hr] using completed_block 56 offset hoff

#print axioms completed_at_56

theorem conditional_at_56 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (435456+offset) =
      min 602 (value Conditional.n5_157 offset) := by
  have hr : lookup Conditional.roots 56 (.leaf 0) = Conditional.n5_157 := by rfl
  simpa only [hr] using conditional_block 56 offset hoff

#print axioms conditional_at_56

theorem completed_at_57 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (443232+offset) =
      min 551 (value Completed.n5_128 offset) := by
  have hr : lookup Completed.roots 57 (.leaf 0) = Completed.n5_128 := by rfl
  simpa only [hr] using completed_block 57 offset hoff

#print axioms completed_at_57

theorem conditional_at_57 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (443232+offset) =
      min 602 (value Conditional.n5_122 offset) := by
  have hr : lookup Conditional.roots 57 (.leaf 0) = Conditional.n5_122 := by rfl
  simpa only [hr] using conditional_block 57 offset hoff

#print axioms conditional_at_57

theorem completed_at_58 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (451008+offset) =
      min 551 (value Completed.n5_138 offset) := by
  have hr : lookup Completed.roots 58 (.leaf 0) = Completed.n5_138 := by rfl
  simpa only [hr] using completed_block 58 offset hoff

#print axioms completed_at_58

theorem conditional_at_58 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (451008+offset) =
      min 602 (value Conditional.n5_133 offset) := by
  have hr : lookup Conditional.roots 58 (.leaf 0) = Conditional.n5_133 := by rfl
  simpa only [hr] using conditional_block 58 offset hoff

#print axioms conditional_at_58

theorem completed_at_59 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (458784+offset) =
      min 551 (value Completed.n5_131 offset) := by
  have hr : lookup Completed.roots 59 (.leaf 0) = Completed.n5_131 := by rfl
  simpa only [hr] using completed_block 59 offset hoff

#print axioms completed_at_59

theorem conditional_at_59 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (458784+offset) =
      min 602 (value Conditional.n5_123 offset) := by
  have hr : lookup Conditional.roots 59 (.leaf 0) = Conditional.n5_123 := by rfl
  simpa only [hr] using conditional_block 59 offset hoff

#print axioms conditional_at_59

theorem completed_at_60 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (466560+offset) =
      min 551 (value Completed.n5_149 offset) := by
  have hr : lookup Completed.roots 60 (.leaf 0) = Completed.n5_149 := by rfl
  simpa only [hr] using completed_block 60 offset hoff

#print axioms completed_at_60

theorem conditional_at_60 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (466560+offset) =
      min 602 (value Conditional.n5_143 offset) := by
  have hr : lookup Conditional.roots 60 (.leaf 0) = Conditional.n5_143 := by rfl
  simpa only [hr] using conditional_block 60 offset hoff

#print axioms conditional_at_60

theorem completed_at_61 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (474336+offset) =
      min 551 (value Completed.n5_148 offset) := by
  have hr : lookup Completed.roots 61 (.leaf 0) = Completed.n5_148 := by rfl
  simpa only [hr] using completed_block 61 offset hoff

#print axioms completed_at_61

theorem conditional_at_61 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (474336+offset) =
      min 602 (value Conditional.n5_142 offset) := by
  have hr : lookup Conditional.roots 61 (.leaf 0) = Conditional.n5_142 := by rfl
  simpa only [hr] using conditional_block 61 offset hoff

#print axioms conditional_at_61

theorem completed_at_62 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (482112+offset) =
      min 551 (value Completed.n5_160 offset) := by
  have hr : lookup Completed.roots 62 (.leaf 0) = Completed.n5_160 := by rfl
  simpa only [hr] using completed_block 62 offset hoff

#print axioms completed_at_62

theorem conditional_at_62 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (482112+offset) =
      min 602 (value Conditional.n5_155 offset) := by
  have hr : lookup Conditional.roots 62 (.leaf 0) = Conditional.n5_155 := by rfl
  simpa only [hr] using conditional_block 62 offset hoff

#print axioms conditional_at_62

theorem completed_at_63 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (489888+offset) =
      min 551 (value Completed.n5_145 offset) := by
  have hr : lookup Completed.roots 63 (.leaf 0) = Completed.n5_145 := by rfl
  simpa only [hr] using completed_block 63 offset hoff

#print axioms completed_at_63

theorem conditional_at_63 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (489888+offset) =
      min 602 (value Conditional.n5_141 offset) := by
  have hr : lookup Conditional.roots 63 (.leaf 0) = Conditional.n5_141 := by rfl
  simpa only [hr] using conditional_block 63 offset hoff

#print axioms conditional_at_63

theorem completed_at_64 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (497664+offset) =
      min 551 (value Completed.n5_171 offset) := by
  have hr : lookup Completed.roots 64 (.leaf 0) = Completed.n5_171 := by rfl
  simpa only [hr] using completed_block 64 offset hoff

#print axioms completed_at_64

theorem conditional_at_64 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (497664+offset) =
      min 602 (value Conditional.n5_167 offset) := by
  have hr : lookup Conditional.roots 64 (.leaf 0) = Conditional.n5_167 := by rfl
  simpa only [hr] using conditional_block 64 offset hoff

#print axioms conditional_at_64

theorem completed_at_65 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (505440+offset) =
      min 551 (value Completed.n5_165 offset) := by
  have hr : lookup Completed.roots 65 (.leaf 0) = Completed.n5_165 := by rfl
  simpa only [hr] using completed_block 65 offset hoff

#print axioms completed_at_65

theorem conditional_at_65 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (505440+offset) =
      min 602 (value Conditional.n5_163 offset) := by
  have hr : lookup Conditional.roots 65 (.leaf 0) = Conditional.n5_163 := by rfl
  simpa only [hr] using conditional_block 65 offset hoff

#print axioms conditional_at_65

theorem completed_at_66 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (513216+offset) =
      min 551 (value Completed.n5_160 offset) := by
  have hr : lookup Completed.roots 66 (.leaf 0) = Completed.n5_160 := by rfl
  simpa only [hr] using completed_block 66 offset hoff

#print axioms completed_at_66

theorem conditional_at_66 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (513216+offset) =
      min 602 (value Conditional.n5_155 offset) := by
  have hr : lookup Conditional.roots 66 (.leaf 0) = Conditional.n5_155 := by rfl
  simpa only [hr] using conditional_block 66 offset hoff

#print axioms conditional_at_66

theorem completed_at_67 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (520992+offset) =
      min 551 (value Completed.n5_118 offset) := by
  have hr : lookup Completed.roots 67 (.leaf 0) = Completed.n5_118 := by rfl
  simpa only [hr] using completed_block 67 offset hoff

#print axioms completed_at_67

theorem conditional_at_67 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (520992+offset) =
      min 602 (value Conditional.n5_114 offset) := by
  have hr : lookup Conditional.roots 67 (.leaf 0) = Conditional.n5_114 := by rfl
  simpa only [hr] using conditional_block 67 offset hoff

#print axioms conditional_at_67

theorem completed_at_68 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (528768+offset) =
      min 551 (value Completed.n5_110 offset) := by
  have hr : lookup Completed.roots 68 (.leaf 0) = Completed.n5_110 := by rfl
  simpa only [hr] using completed_block 68 offset hoff

#print axioms completed_at_68

theorem conditional_at_68 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (528768+offset) =
      min 602 (value Conditional.n5_102 offset) := by
  have hr : lookup Conditional.roots 68 (.leaf 0) = Conditional.n5_102 := by rfl
  simpa only [hr] using conditional_block 68 offset hoff

#print axioms conditional_at_68

theorem completed_at_69 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (536544+offset) =
      min 551 (value Completed.n5_95 offset) := by
  have hr : lookup Completed.roots 69 (.leaf 0) = Completed.n5_95 := by rfl
  simpa only [hr] using completed_block 69 offset hoff

#print axioms completed_at_69

theorem conditional_at_69 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (536544+offset) =
      min 602 (value Conditional.n5_95 offset) := by
  have hr : lookup Conditional.roots 69 (.leaf 0) = Conditional.n5_95 := by rfl
  simpa only [hr] using conditional_block 69 offset hoff

#print axioms conditional_at_69

theorem completed_at_70 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (544320+offset) =
      min 551 (value Completed.n5_107 offset) := by
  have hr : lookup Completed.roots 70 (.leaf 0) = Completed.n5_107 := by rfl
  simpa only [hr] using completed_block 70 offset hoff

#print axioms completed_at_70

theorem conditional_at_70 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (544320+offset) =
      min 602 (value Conditional.n5_109 offset) := by
  have hr : lookup Conditional.roots 70 (.leaf 0) = Conditional.n5_109 := by rfl
  simpa only [hr] using conditional_block 70 offset hoff

#print axioms conditional_at_70

theorem completed_at_71 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (552096+offset) =
      min 551 (value Completed.n5_130 offset) := by
  have hr : lookup Completed.roots 71 (.leaf 0) = Completed.n5_130 := by rfl
  simpa only [hr] using completed_block 71 offset hoff

#print axioms completed_at_71

theorem conditional_at_71 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (552096+offset) =
      min 602 (value Conditional.n5_126 offset) := by
  have hr : lookup Conditional.roots 71 (.leaf 0) = Conditional.n5_126 := by rfl
  simpa only [hr] using conditional_block 71 offset hoff

#print axioms conditional_at_71

theorem completed_at_72 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (559872+offset) =
      min 551 (value Completed.n5_124 offset) := by
  have hr : lookup Completed.roots 72 (.leaf 0) = Completed.n5_124 := by rfl
  simpa only [hr] using completed_block 72 offset hoff

#print axioms completed_at_72

theorem conditional_at_72 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (559872+offset) =
      min 602 (value Conditional.n5_119 offset) := by
  have hr : lookup Conditional.roots 72 (.leaf 0) = Conditional.n5_119 := by rfl
  simpa only [hr] using conditional_block 72 offset hoff

#print axioms conditional_at_72

theorem completed_at_73 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (567648+offset) =
      min 551 (value Completed.n5_137 offset) := by
  have hr : lookup Completed.roots 73 (.leaf 0) = Completed.n5_137 := by rfl
  simpa only [hr] using completed_block 73 offset hoff

#print axioms completed_at_73

theorem conditional_at_73 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (567648+offset) =
      min 602 (value Conditional.n5_132 offset) := by
  have hr : lookup Conditional.roots 73 (.leaf 0) = Conditional.n5_132 := by rfl
  simpa only [hr] using conditional_block 73 offset hoff

#print axioms conditional_at_73

theorem completed_at_74 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (575424+offset) =
      min 551 (value Completed.n5_129 offset) := by
  have hr : lookup Completed.roots 74 (.leaf 0) = Completed.n5_129 := by rfl
  simpa only [hr] using completed_block 74 offset hoff

#print axioms completed_at_74

theorem conditional_at_74 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (575424+offset) =
      min 602 (value Conditional.n5_125 offset) := by
  have hr : lookup Conditional.roots 74 (.leaf 0) = Conditional.n5_125 := by rfl
  simpa only [hr] using conditional_block 74 offset hoff

#print axioms conditional_at_74

theorem completed_at_75 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (583200+offset) =
      min 551 (value Completed.n5_39 offset) := by
  have hr : lookup Completed.roots 75 (.leaf 0) = Completed.n5_39 := by rfl
  simpa only [hr] using completed_block 75 offset hoff

#print axioms completed_at_75

theorem conditional_at_75 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (583200+offset) =
      min 602 (value Conditional.n5_41 offset) := by
  have hr : lookup Conditional.roots 75 (.leaf 0) = Conditional.n5_41 := by rfl
  simpa only [hr] using conditional_block 75 offset hoff

#print axioms conditional_at_75

theorem completed_at_76 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (590976+offset) =
      min 551 (value Completed.n5_25 offset) := by
  have hr : lookup Completed.roots 76 (.leaf 0) = Completed.n5_25 := by rfl
  simpa only [hr] using completed_block 76 offset hoff

#print axioms completed_at_76

theorem conditional_at_76 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (590976+offset) =
      min 602 (value Conditional.n5_27 offset) := by
  have hr : lookup Conditional.roots 76 (.leaf 0) = Conditional.n5_27 := by rfl
  simpa only [hr] using conditional_block 76 offset hoff

#print axioms conditional_at_76

theorem completed_at_77 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (598752+offset) =
      min 551 (value Completed.n5_26 offset) := by
  have hr : lookup Completed.roots 77 (.leaf 0) = Completed.n5_26 := by rfl
  simpa only [hr] using completed_block 77 offset hoff

#print axioms completed_at_77

theorem conditional_at_77 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (598752+offset) =
      min 602 (value Conditional.n5_38 offset) := by
  have hr : lookup Conditional.roots 77 (.leaf 0) = Conditional.n5_38 := by rfl
  simpa only [hr] using conditional_block 77 offset hoff

#print axioms conditional_at_77

theorem completed_at_78 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (606528+offset) =
      min 551 (value Completed.n5_78 offset) := by
  have hr : lookup Completed.roots 78 (.leaf 0) = Completed.n5_78 := by rfl
  simpa only [hr] using completed_block 78 offset hoff

#print axioms completed_at_78

theorem conditional_at_78 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (606528+offset) =
      min 602 (value Conditional.n5_73 offset) := by
  have hr : lookup Conditional.roots 78 (.leaf 0) = Conditional.n5_73 := by rfl
  simpa only [hr] using conditional_block 78 offset hoff

#print axioms conditional_at_78

theorem completed_at_79 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (614304+offset) =
      min 551 (value Completed.n5_100 offset) := by
  have hr : lookup Completed.roots 79 (.leaf 0) = Completed.n5_100 := by rfl
  simpa only [hr] using completed_block 79 offset hoff

#print axioms completed_at_79

theorem conditional_at_79 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (614304+offset) =
      min 602 (value Conditional.n5_106 offset) := by
  have hr : lookup Conditional.roots 79 (.leaf 0) = Conditional.n5_106 := by rfl
  simpa only [hr] using conditional_block 79 offset hoff

#print axioms conditional_at_79

theorem completed_at_80 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (622080+offset) =
      min 551 (value Completed.n5_70 offset) := by
  have hr : lookup Completed.roots 80 (.leaf 0) = Completed.n5_70 := by rfl
  simpa only [hr] using completed_block 80 offset hoff

#print axioms completed_at_80

theorem conditional_at_80 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (622080+offset) =
      min 602 (value Conditional.n5_68 offset) := by
  have hr : lookup Conditional.roots 80 (.leaf 0) = Conditional.n5_68 := by rfl
  simpa only [hr] using conditional_block 80 offset hoff

#print axioms conditional_at_80

theorem completed_at_81 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (629856+offset) =
      min 551 (value Completed.n5_53 offset) := by
  have hr : lookup Completed.roots 81 (.leaf 0) = Completed.n5_53 := by rfl
  simpa only [hr] using completed_block 81 offset hoff

#print axioms completed_at_81

theorem conditional_at_81 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (629856+offset) =
      min 602 (value Conditional.n5_54 offset) := by
  have hr : lookup Conditional.roots 81 (.leaf 0) = Conditional.n5_54 := by rfl
  simpa only [hr] using conditional_block 81 offset hoff

#print axioms conditional_at_81

theorem completed_at_82 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (637632+offset) =
      min 551 (value Completed.n5_68 offset) := by
  have hr : lookup Completed.roots 82 (.leaf 0) = Completed.n5_68 := by rfl
  simpa only [hr] using completed_block 82 offset hoff

#print axioms completed_at_82

theorem conditional_at_82 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (637632+offset) =
      min 602 (value Conditional.n5_65 offset) := by
  have hr : lookup Conditional.roots 82 (.leaf 0) = Conditional.n5_65 := by rfl
  simpa only [hr] using conditional_block 82 offset hoff

#print axioms conditional_at_82

theorem completed_at_83 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (645408+offset) =
      min 551 (value Completed.n5_122 offset) := by
  have hr : lookup Completed.roots 83 (.leaf 0) = Completed.n5_122 := by rfl
  simpa only [hr] using completed_block 83 offset hoff

#print axioms completed_at_83

theorem conditional_at_83 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (645408+offset) =
      min 602 (value Conditional.n5_117 offset) := by
  have hr : lookup Conditional.roots 83 (.leaf 0) = Conditional.n5_117 := by rfl
  simpa only [hr] using conditional_block 83 offset hoff

#print axioms conditional_at_83

theorem completed_at_84 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (653184+offset) =
      min 551 (value Completed.n5_23 offset) := by
  have hr : lookup Completed.roots 84 (.leaf 0) = Completed.n5_23 := by rfl
  simpa only [hr] using completed_block 84 offset hoff

#print axioms completed_at_84

theorem conditional_at_84 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (653184+offset) =
      min 602 (value Conditional.n5_24 offset) := by
  have hr : lookup Conditional.roots 84 (.leaf 0) = Conditional.n5_24 := by rfl
  simpa only [hr] using conditional_block 84 offset hoff

#print axioms conditional_at_84

theorem completed_at_85 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (660960+offset) =
      min 551 (value Completed.n5_14 offset) := by
  have hr : lookup Completed.roots 85 (.leaf 0) = Completed.n5_14 := by rfl
  simpa only [hr] using completed_block 85 offset hoff

#print axioms completed_at_85

theorem conditional_at_85 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (660960+offset) =
      min 602 (value Conditional.n5_14 offset) := by
  have hr : lookup Conditional.roots 85 (.leaf 0) = Conditional.n5_14 := by rfl
  simpa only [hr] using conditional_block 85 offset hoff

#print axioms conditional_at_85

theorem completed_at_86 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (668736+offset) =
      min 551 (value Completed.n5_24 offset) := by
  have hr : lookup Completed.roots 86 (.leaf 0) = Completed.n5_24 := by rfl
  simpa only [hr] using completed_block 86 offset hoff

#print axioms completed_at_86

theorem conditional_at_86 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (668736+offset) =
      min 602 (value Conditional.n5_23 offset) := by
  have hr : lookup Conditional.roots 86 (.leaf 0) = Conditional.n5_23 := by rfl
  simpa only [hr] using conditional_block 86 offset hoff

#print axioms conditional_at_86

theorem completed_at_87 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (676512+offset) =
      min 551 (value Completed.n5_2 offset) := by
  have hr : lookup Completed.roots 87 (.leaf 0) = Completed.n5_2 := by rfl
  simpa only [hr] using completed_block 87 offset hoff

#print axioms completed_at_87

theorem conditional_at_87 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (676512+offset) =
      min 602 (value Conditional.n5_3 offset) := by
  have hr : lookup Conditional.roots 87 (.leaf 0) = Conditional.n5_3 := by rfl
  simpa only [hr] using conditional_block 87 offset hoff

#print axioms conditional_at_87

theorem completed_at_88 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (684288+offset) =
      min 551 (value Completed.n5_0 offset) := by
  have hr : lookup Completed.roots 88 (.leaf 0) = Completed.n5_0 := by rfl
  simpa only [hr] using completed_block 88 offset hoff

#print axioms completed_at_88

theorem conditional_at_88 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (684288+offset) =
      min 602 (value Conditional.n5_1 offset) := by
  have hr : lookup Conditional.roots 88 (.leaf 0) = Conditional.n5_1 := by rfl
  simpa only [hr] using conditional_block 88 offset hoff

#print axioms conditional_at_88

theorem completed_at_89 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (692064+offset) =
      min 551 (value Completed.n5_7 offset) := by
  have hr : lookup Completed.roots 89 (.leaf 0) = Completed.n5_7 := by rfl
  simpa only [hr] using completed_block 89 offset hoff

#print axioms completed_at_89

theorem conditional_at_89 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (692064+offset) =
      min 602 (value Conditional.n5_7 offset) := by
  have hr : lookup Conditional.roots 89 (.leaf 0) = Conditional.n5_7 := by rfl
  simpa only [hr] using conditional_block 89 offset hoff

#print axioms conditional_at_89

theorem completed_at_90 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (699840+offset) =
      min 551 (value Completed.n5_6 offset) := by
  have hr : lookup Completed.roots 90 (.leaf 0) = Completed.n5_6 := by rfl
  simpa only [hr] using completed_block 90 offset hoff

#print axioms completed_at_90

theorem conditional_at_90 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (699840+offset) =
      min 602 (value Conditional.n5_6 offset) := by
  have hr : lookup Conditional.roots 90 (.leaf 0) = Conditional.n5_6 := by rfl
  simpa only [hr] using conditional_block 90 offset hoff

#print axioms conditional_at_90

theorem completed_at_91 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (707616+offset) =
      min 551 (value Completed.n5_20 offset) := by
  have hr : lookup Completed.roots 91 (.leaf 0) = Completed.n5_20 := by rfl
  simpa only [hr] using completed_block 91 offset hoff

#print axioms completed_at_91

theorem conditional_at_91 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (707616+offset) =
      min 602 (value Conditional.n5_22 offset) := by
  have hr : lookup Conditional.roots 91 (.leaf 0) = Conditional.n5_22 := by rfl
  simpa only [hr] using conditional_block 91 offset hoff

#print axioms conditional_at_91

theorem completed_at_92 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (715392+offset) =
      min 551 (value Completed.n5_121 offset) := by
  have hr : lookup Completed.roots 92 (.leaf 0) = Completed.n5_121 := by rfl
  simpa only [hr] using completed_block 92 offset hoff

#print axioms completed_at_92

theorem conditional_at_92 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (715392+offset) =
      min 602 (value Conditional.n5_116 offset) := by
  have hr : lookup Conditional.roots 92 (.leaf 0) = Conditional.n5_116 := by rfl
  simpa only [hr] using conditional_block 92 offset hoff

#print axioms conditional_at_92

theorem completed_at_93 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (723168+offset) =
      min 551 (value Completed.n5_22 offset) := by
  have hr : lookup Completed.roots 93 (.leaf 0) = Completed.n5_22 := by rfl
  simpa only [hr] using completed_block 93 offset hoff

#print axioms completed_at_93

theorem conditional_at_93 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (723168+offset) =
      min 602 (value Conditional.n5_21 offset) := by
  have hr : lookup Conditional.roots 93 (.leaf 0) = Conditional.n5_21 := by rfl
  simpa only [hr] using conditional_block 93 offset hoff

#print axioms conditional_at_93

theorem completed_at_94 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (730944+offset) =
      min 551 (value Completed.n5_13 offset) := by
  have hr : lookup Completed.roots 94 (.leaf 0) = Completed.n5_13 := by rfl
  simpa only [hr] using completed_block 94 offset hoff

#print axioms completed_at_94

theorem conditional_at_94 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (730944+offset) =
      min 602 (value Conditional.n5_13 offset) := by
  have hr : lookup Conditional.roots 94 (.leaf 0) = Conditional.n5_13 := by rfl
  simpa only [hr] using conditional_block 94 offset hoff

#print axioms conditional_at_94

theorem completed_at_95 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (738720+offset) =
      min 551 (value Completed.n5_20 offset) := by
  have hr : lookup Completed.roots 95 (.leaf 0) = Completed.n5_20 := by rfl
  simpa only [hr] using completed_block 95 offset hoff

#print axioms completed_at_95

theorem conditional_at_95 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (738720+offset) =
      min 602 (value Conditional.n5_22 offset) := by
  have hr : lookup Conditional.roots 95 (.leaf 0) = Conditional.n5_22 := by rfl
  simpa only [hr] using conditional_block 95 offset hoff

#print axioms conditional_at_95

theorem completed_at_96 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (746496+offset) =
      min 551 (value Completed.n5_72 offset) := by
  have hr : lookup Completed.roots 96 (.leaf 0) = Completed.n5_72 := by rfl
  simpa only [hr] using completed_block 96 offset hoff

#print axioms completed_at_96

theorem conditional_at_96 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (746496+offset) =
      min 602 (value Conditional.n5_84 offset) := by
  have hr : lookup Conditional.roots 96 (.leaf 0) = Conditional.n5_84 := by rfl
  simpa only [hr] using conditional_block 96 offset hoff

#print axioms conditional_at_96

theorem completed_at_97 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (754272+offset) =
      min 551 (value Completed.n5_75 offset) := by
  have hr : lookup Completed.roots 97 (.leaf 0) = Completed.n5_75 := by rfl
  simpa only [hr] using completed_block 97 offset hoff

#print axioms completed_at_97

theorem conditional_at_97 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (754272+offset) =
      min 602 (value Conditional.n5_85 offset) := by
  have hr : lookup Conditional.roots 97 (.leaf 0) = Conditional.n5_85 := by rfl
  simpa only [hr] using conditional_block 97 offset hoff

#print axioms conditional_at_97

theorem completed_at_98 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (762048+offset) =
      min 551 (value Completed.n5_30 offset) := by
  have hr : lookup Completed.roots 98 (.leaf 0) = Completed.n5_30 := by rfl
  simpa only [hr] using completed_block 98 offset hoff

#print axioms completed_at_98

theorem conditional_at_98 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (762048+offset) =
      min 602 (value Conditional.n5_44 offset) := by
  have hr : lookup Conditional.roots 98 (.leaf 0) = Conditional.n5_44 := by rfl
  simpa only [hr] using conditional_block 98 offset hoff

#print axioms conditional_at_98

theorem completed_at_99 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (769824+offset) =
      min 551 (value Completed.n5_77 offset) := by
  have hr : lookup Completed.roots 99 (.leaf 0) = Completed.n5_77 := by rfl
  simpa only [hr] using completed_block 99 offset hoff

#print axioms completed_at_99

theorem conditional_at_99 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (769824+offset) =
      min 602 (value Conditional.n5_86 offset) := by
  have hr : lookup Conditional.roots 99 (.leaf 0) = Conditional.n5_86 := by rfl
  simpa only [hr] using conditional_block 99 offset hoff

#print axioms conditional_at_99

theorem completed_at_100 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (777600+offset) =
      min 551 (value Completed.n5_65 offset) := by
  have hr : lookup Completed.roots 100 (.leaf 0) = Completed.n5_65 := by rfl
  simpa only [hr] using completed_block 100 offset hoff

#print axioms completed_at_100

theorem conditional_at_100 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (777600+offset) =
      min 602 (value Conditional.n5_70 offset) := by
  have hr : lookup Conditional.roots 100 (.leaf 0) = Conditional.n5_70 := by rfl
  simpa only [hr] using conditional_block 100 offset hoff

#print axioms conditional_at_100

theorem completed_at_101 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (785376+offset) =
      min 551 (value Completed.n5_176 offset) := by
  have hr : lookup Completed.roots 101 (.leaf 0) = Completed.n5_176 := by rfl
  simpa only [hr] using completed_block 101 offset hoff

#print axioms completed_at_101

theorem conditional_at_101 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (785376+offset) =
      min 602 (value Conditional.n5_170 offset) := by
  have hr : lookup Conditional.roots 101 (.leaf 0) = Conditional.n5_170 := by rfl
  simpa only [hr] using conditional_block 101 offset hoff

#print axioms conditional_at_101

theorem completed_at_102 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (793152+offset) =
      min 551 (value Completed.n5_67 offset) := by
  have hr : lookup Completed.roots 102 (.leaf 0) = Completed.n5_67 := by rfl
  simpa only [hr] using completed_block 102 offset hoff

#print axioms completed_at_102

theorem conditional_at_102 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (793152+offset) =
      min 602 (value Conditional.n5_83 offset) := by
  have hr : lookup Conditional.roots 102 (.leaf 0) = Conditional.n5_83 := by rfl
  simpa only [hr] using conditional_block 102 offset hoff

#print axioms conditional_at_102

theorem completed_at_103 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (800928+offset) =
      min 551 (value Completed.n5_67 offset) := by
  have hr : lookup Completed.roots 103 (.leaf 0) = Completed.n5_67 := by rfl
  simpa only [hr] using completed_block 103 offset hoff

#print axioms completed_at_103

theorem conditional_at_103 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (800928+offset) =
      min 602 (value Conditional.n5_83 offset) := by
  have hr : lookup Conditional.roots 103 (.leaf 0) = Conditional.n5_83 := by rfl
  simpa only [hr] using conditional_block 103 offset hoff

#print axioms conditional_at_103

end Snake9.PotentialBlocks102
