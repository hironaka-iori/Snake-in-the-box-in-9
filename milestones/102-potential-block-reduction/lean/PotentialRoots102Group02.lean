import PotentialBlocks102

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.PotentialBlocks102
open Snake9.Potential99 Snake9.Balanced89

theorem completed_at_104 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (808704+offset) =
      min 551 (value Completed.n5_71 offset) := by
  have hr : lookup Completed.roots 104 (.leaf 0) = Completed.n5_71 := by rfl
  simpa only [hr] using completed_block 104 offset hoff

#print axioms completed_at_104

theorem conditional_at_104 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (808704+offset) =
      min 602 (value Conditional.n5_80 offset) := by
  have hr : lookup Conditional.roots 104 (.leaf 0) = Conditional.n5_80 := by rfl
  simpa only [hr] using conditional_block 104 offset hoff

#print axioms conditional_at_104

theorem completed_at_105 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (816480+offset) =
      min 551 (value Completed.n5_27 offset) := by
  have hr : lookup Completed.roots 105 (.leaf 0) = Completed.n5_27 := by rfl
  simpa only [hr] using completed_block 105 offset hoff

#print axioms completed_at_105

theorem conditional_at_105 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (816480+offset) =
      min 602 (value Conditional.n5_39 offset) := by
  have hr : lookup Conditional.roots 105 (.leaf 0) = Conditional.n5_39 := by rfl
  simpa only [hr] using conditional_block 105 offset hoff

#print axioms conditional_at_105

theorem completed_at_106 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (824256+offset) =
      min 551 (value Completed.n5_67 offset) := by
  have hr : lookup Completed.roots 106 (.leaf 0) = Completed.n5_67 := by rfl
  simpa only [hr] using completed_block 106 offset hoff

#print axioms completed_at_106

theorem conditional_at_106 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (824256+offset) =
      min 602 (value Conditional.n5_83 offset) := by
  have hr : lookup Conditional.roots 106 (.leaf 0) = Conditional.n5_83 := by rfl
  simpa only [hr] using conditional_block 106 offset hoff

#print axioms conditional_at_106

theorem completed_at_107 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (832032+offset) =
      min 551 (value Completed.n5_74 offset) := by
  have hr : lookup Completed.roots 107 (.leaf 0) = Completed.n5_74 := by rfl
  simpa only [hr] using completed_block 107 offset hoff

#print axioms completed_at_107

theorem conditional_at_107 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (832032+offset) =
      min 602 (value Conditional.n5_64 offset) := by
  have hr : lookup Conditional.roots 107 (.leaf 0) = Conditional.n5_64 := by rfl
  simpa only [hr] using conditional_block 107 offset hoff

#print axioms conditional_at_107

theorem completed_at_108 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (839808+offset) =
      min 551 (value Completed.n5_102 offset) := by
  have hr : lookup Completed.roots 108 (.leaf 0) = Completed.n5_102 := by rfl
  simpa only [hr] using completed_block 108 offset hoff

#print axioms completed_at_108

theorem conditional_at_108 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (839808+offset) =
      min 602 (value Conditional.n5_105 offset) := by
  have hr : lookup Conditional.roots 108 (.leaf 0) = Conditional.n5_105 := by rfl
  simpa only [hr] using conditional_block 108 offset hoff

#print axioms conditional_at_108

theorem completed_at_109 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (847584+offset) =
      min 551 (value Completed.n5_76 offset) := by
  have hr : lookup Completed.roots 109 (.leaf 0) = Completed.n5_76 := by rfl
  simpa only [hr] using completed_block 109 offset hoff

#print axioms completed_at_109

theorem conditional_at_109 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (847584+offset) =
      min 602 (value Conditional.n5_67 offset) := by
  have hr : lookup Conditional.roots 109 (.leaf 0) = Conditional.n5_67 := by rfl
  simpa only [hr] using conditional_block 109 offset hoff

#print axioms conditional_at_109

theorem completed_at_110 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (855360+offset) =
      min 551 (value Completed.n5_55 offset) := by
  have hr : lookup Completed.roots 110 (.leaf 0) = Completed.n5_55 := by rfl
  simpa only [hr] using completed_block 110 offset hoff

#print axioms completed_at_110

theorem conditional_at_110 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (855360+offset) =
      min 602 (value Conditional.n5_53 offset) := by
  have hr : lookup Conditional.roots 110 (.leaf 0) = Conditional.n5_53 := by rfl
  simpa only [hr] using conditional_block 110 offset hoff

#print axioms conditional_at_110

theorem completed_at_111 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (863136+offset) =
      min 551 (value Completed.n5_74 offset) := by
  have hr : lookup Completed.roots 111 (.leaf 0) = Completed.n5_74 := by rfl
  simpa only [hr] using completed_block 111 offset hoff

#print axioms completed_at_111

theorem conditional_at_111 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (863136+offset) =
      min 602 (value Conditional.n5_64 offset) := by
  have hr : lookup Conditional.roots 111 (.leaf 0) = Conditional.n5_64 := by rfl
  simpa only [hr] using conditional_block 111 offset hoff

#print axioms conditional_at_111

theorem completed_at_112 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (870912+offset) =
      min 551 (value Completed.n5_106 offset) := by
  have hr : lookup Completed.roots 112 (.leaf 0) = Completed.n5_106 := by rfl
  simpa only [hr] using completed_block 112 offset hoff

#print axioms completed_at_112

theorem conditional_at_112 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (870912+offset) =
      min 602 (value Conditional.n5_100 offset) := by
  have hr : lookup Conditional.roots 112 (.leaf 0) = Conditional.n5_100 := by rfl
  simpa only [hr] using conditional_block 112 offset hoff

#print axioms conditional_at_112

theorem completed_at_113 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (878688+offset) =
      min 551 (value Completed.n5_99 offset) := by
  have hr : lookup Completed.roots 113 (.leaf 0) = Completed.n5_99 := by rfl
  simpa only [hr] using completed_block 113 offset hoff

#print axioms completed_at_113

theorem conditional_at_113 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (878688+offset) =
      min 602 (value Conditional.n5_113 offset) := by
  have hr : lookup Conditional.roots 113 (.leaf 0) = Conditional.n5_113 := by rfl
  simpa only [hr] using conditional_block 113 offset hoff

#print axioms conditional_at_113

theorem completed_at_114 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (886464+offset) =
      min 551 (value Completed.n5_111 offset) := by
  have hr : lookup Completed.roots 114 (.leaf 0) = Completed.n5_111 := by rfl
  simpa only [hr] using completed_block 114 offset hoff

#print axioms completed_at_114

theorem conditional_at_114 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (886464+offset) =
      min 602 (value Conditional.n5_101 offset) := by
  have hr : lookup Conditional.roots 114 (.leaf 0) = Conditional.n5_101 := by rfl
  simpa only [hr] using conditional_block 114 offset hoff

#print axioms conditional_at_114

theorem completed_at_115 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (894240+offset) =
      min 551 (value Completed.n5_93 offset) := by
  have hr : lookup Completed.roots 115 (.leaf 0) = Completed.n5_93 := by rfl
  simpa only [hr] using completed_block 115 offset hoff

#print axioms completed_at_115

theorem conditional_at_115 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (894240+offset) =
      min 602 (value Conditional.n5_94 offset) := by
  have hr : lookup Conditional.roots 115 (.leaf 0) = Conditional.n5_94 := by rfl
  simpa only [hr] using conditional_block 115 offset hoff

#print axioms conditional_at_115

theorem completed_at_116 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (902016+offset) =
      min 551 (value Completed.n5_106 offset) := by
  have hr : lookup Completed.roots 116 (.leaf 0) = Completed.n5_106 := by rfl
  simpa only [hr] using completed_block 116 offset hoff

#print axioms completed_at_116

theorem conditional_at_116 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (902016+offset) =
      min 602 (value Conditional.n5_100 offset) := by
  have hr : lookup Conditional.roots 116 (.leaf 0) = Conditional.n5_100 := by rfl
  simpa only [hr] using conditional_block 116 offset hoff

#print axioms conditional_at_116

theorem completed_at_117 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (909792+offset) =
      min 551 (value Completed.n5_132 offset) := by
  have hr : lookup Completed.roots 117 (.leaf 0) = Completed.n5_132 := by rfl
  simpa only [hr] using completed_block 117 offset hoff

#print axioms completed_at_117

theorem conditional_at_117 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (909792+offset) =
      min 602 (value Conditional.n5_124 offset) := by
  have hr : lookup Conditional.roots 117 (.leaf 0) = Conditional.n5_124 := by rfl
  simpa only [hr] using conditional_block 117 offset hoff

#print axioms conditional_at_117

theorem completed_at_118 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (917568+offset) =
      min 551 (value Completed.n5_132 offset) := by
  have hr : lookup Completed.roots 118 (.leaf 0) = Completed.n5_132 := by rfl
  simpa only [hr] using completed_block 118 offset hoff

#print axioms completed_at_118

theorem conditional_at_118 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (917568+offset) =
      min 602 (value Conditional.n5_124 offset) := by
  have hr : lookup Conditional.roots 118 (.leaf 0) = Conditional.n5_124 := by rfl
  simpa only [hr] using conditional_block 118 offset hoff

#print axioms conditional_at_118

theorem completed_at_119 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (925344+offset) =
      min 551 (value Completed.n5_150 offset) := by
  have hr : lookup Completed.roots 119 (.leaf 0) = Completed.n5_150 := by rfl
  simpa only [hr] using completed_block 119 offset hoff

#print axioms completed_at_119

theorem conditional_at_119 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (925344+offset) =
      min 602 (value Conditional.n5_145 offset) := by
  have hr : lookup Conditional.roots 119 (.leaf 0) = Conditional.n5_145 := by rfl
  simpa only [hr] using conditional_block 119 offset hoff

#print axioms conditional_at_119

theorem completed_at_120 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (933120+offset) =
      min 551 (value Completed.n5_139 offset) := by
  have hr : lookup Completed.roots 120 (.leaf 0) = Completed.n5_139 := by rfl
  simpa only [hr] using completed_block 120 offset hoff

#print axioms completed_at_120

theorem conditional_at_120 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (933120+offset) =
      min 602 (value Conditional.n5_131 offset) := by
  have hr : lookup Conditional.roots 120 (.leaf 0) = Conditional.n5_131 := by rfl
  simpa only [hr] using conditional_block 120 offset hoff

#print axioms conditional_at_120

theorem completed_at_121 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (940896+offset) =
      min 551 (value Completed.n5_132 offset) := by
  have hr : lookup Completed.roots 121 (.leaf 0) = Completed.n5_132 := by rfl
  simpa only [hr] using completed_block 121 offset hoff

#print axioms completed_at_121

theorem conditional_at_121 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (940896+offset) =
      min 602 (value Conditional.n5_124 offset) := by
  have hr : lookup Conditional.roots 121 (.leaf 0) = Conditional.n5_124 := by rfl
  simpa only [hr] using conditional_block 121 offset hoff

#print axioms conditional_at_121

theorem completed_at_122 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (948672+offset) =
      min 551 (value Completed.n5_29 offset) := by
  have hr : lookup Completed.roots 122 (.leaf 0) = Completed.n5_29 := by rfl
  simpa only [hr] using completed_block 122 offset hoff

#print axioms completed_at_122

theorem conditional_at_122 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (948672+offset) =
      min 602 (value Conditional.n5_37 offset) := by
  have hr : lookup Conditional.roots 122 (.leaf 0) = Conditional.n5_37 := by rfl
  simpa only [hr] using conditional_block 122 offset hoff

#print axioms conditional_at_122

theorem completed_at_123 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (956448+offset) =
      min 551 (value Completed.n5_29 offset) := by
  have hr : lookup Completed.roots 123 (.leaf 0) = Completed.n5_29 := by rfl
  simpa only [hr] using completed_block 123 offset hoff

#print axioms completed_at_123

theorem conditional_at_123 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (956448+offset) =
      min 602 (value Conditional.n5_37 offset) := by
  have hr : lookup Conditional.roots 123 (.leaf 0) = Conditional.n5_37 := by rfl
  simpa only [hr] using conditional_block 123 offset hoff

#print axioms conditional_at_123

theorem completed_at_124 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (964224+offset) =
      min 551 (value Completed.n5_28 offset) := by
  have hr : lookup Completed.roots 124 (.leaf 0) = Completed.n5_28 := by rfl
  simpa only [hr] using completed_block 124 offset hoff

#print axioms completed_at_124

theorem conditional_at_124 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (964224+offset) =
      min 602 (value Conditional.n5_28 offset) := by
  have hr : lookup Conditional.roots 124 (.leaf 0) = Conditional.n5_28 := by rfl
  simpa only [hr] using conditional_block 124 offset hoff

#print axioms conditional_at_124

theorem completed_at_125 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (972000+offset) =
      min 551 (value Completed.n5_29 offset) := by
  have hr : lookup Completed.roots 125 (.leaf 0) = Completed.n5_29 := by rfl
  simpa only [hr] using completed_block 125 offset hoff

#print axioms completed_at_125

theorem conditional_at_125 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (972000+offset) =
      min 602 (value Conditional.n5_37 offset) := by
  have hr : lookup Conditional.roots 125 (.leaf 0) = Conditional.n5_37 := by rfl
  simpa only [hr] using conditional_block 125 offset hoff

#print axioms conditional_at_125

theorem completed_at_126 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (979776+offset) =
      min 551 (value Completed.n5_74 offset) := by
  have hr : lookup Completed.roots 126 (.leaf 0) = Completed.n5_74 := by rfl
  simpa only [hr] using completed_block 126 offset hoff

#print axioms completed_at_126

theorem conditional_at_126 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (979776+offset) =
      min 602 (value Conditional.n5_64 offset) := by
  have hr : lookup Conditional.roots 126 (.leaf 0) = Conditional.n5_64 := by rfl
  simpa only [hr] using conditional_block 126 offset hoff

#print axioms conditional_at_126

theorem completed_at_127 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (987552+offset) =
      min 551 (value Completed.n5_74 offset) := by
  have hr : lookup Completed.roots 127 (.leaf 0) = Completed.n5_74 := by rfl
  simpa only [hr] using completed_block 127 offset hoff

#print axioms completed_at_127

theorem conditional_at_127 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (987552+offset) =
      min 602 (value Conditional.n5_64 offset) := by
  have hr : lookup Conditional.roots 127 (.leaf 0) = Conditional.n5_64 := by rfl
  simpa only [hr] using conditional_block 127 offset hoff

#print axioms conditional_at_127

theorem completed_at_128 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (995328+offset) =
      min 551 (value Completed.n5_102 offset) := by
  have hr : lookup Completed.roots 128 (.leaf 0) = Completed.n5_102 := by rfl
  simpa only [hr] using completed_block 128 offset hoff

#print axioms completed_at_128

theorem conditional_at_128 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (995328+offset) =
      min 602 (value Conditional.n5_105 offset) := by
  have hr : lookup Conditional.roots 128 (.leaf 0) = Conditional.n5_105 := by rfl
  simpa only [hr] using conditional_block 128 offset hoff

#print axioms conditional_at_128

theorem completed_at_129 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1003104+offset) =
      min 551 (value Completed.n5_76 offset) := by
  have hr : lookup Completed.roots 129 (.leaf 0) = Completed.n5_76 := by rfl
  simpa only [hr] using completed_block 129 offset hoff

#print axioms completed_at_129

theorem conditional_at_129 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1003104+offset) =
      min 602 (value Conditional.n5_67 offset) := by
  have hr : lookup Conditional.roots 129 (.leaf 0) = Conditional.n5_67 := by rfl
  simpa only [hr] using conditional_block 129 offset hoff

#print axioms conditional_at_129

theorem completed_at_130 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1010880+offset) =
      min 551 (value Completed.n5_54 offset) := by
  have hr : lookup Completed.roots 130 (.leaf 0) = Completed.n5_54 := by rfl
  simpa only [hr] using completed_block 130 offset hoff

#print axioms completed_at_130

theorem conditional_at_130 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1010880+offset) =
      min 602 (value Conditional.n5_53 offset) := by
  have hr : lookup Conditional.roots 130 (.leaf 0) = Conditional.n5_53 := by rfl
  simpa only [hr] using conditional_block 130 offset hoff

#print axioms conditional_at_130

theorem completed_at_131 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1018656+offset) =
      min 551 (value Completed.n5_74 offset) := by
  have hr : lookup Completed.roots 131 (.leaf 0) = Completed.n5_74 := by rfl
  simpa only [hr] using completed_block 131 offset hoff

#print axioms completed_at_131

theorem conditional_at_131 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1018656+offset) =
      min 602 (value Conditional.n5_64 offset) := by
  have hr : lookup Conditional.roots 131 (.leaf 0) = Conditional.n5_64 := by rfl
  simpa only [hr] using conditional_block 131 offset hoff

#print axioms conditional_at_131

theorem completed_at_132 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1026432+offset) =
      min 551 (value Completed.n5_162 offset) := by
  have hr : lookup Completed.roots 132 (.leaf 0) = Completed.n5_162 := by rfl
  simpa only [hr] using completed_block 132 offset hoff

#print axioms completed_at_132

theorem conditional_at_132 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1026432+offset) =
      min 602 (value Conditional.n5_156 offset) := by
  have hr : lookup Conditional.roots 132 (.leaf 0) = Conditional.n5_156 := by rfl
  simpa only [hr] using conditional_block 132 offset hoff

#print axioms conditional_at_132

theorem completed_at_133 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1034208+offset) =
      min 551 (value Completed.n5_146 offset) := by
  have hr : lookup Completed.roots 133 (.leaf 0) = Completed.n5_146 := by rfl
  simpa only [hr] using completed_block 133 offset hoff

#print axioms completed_at_133

theorem conditional_at_133 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1034208+offset) =
      min 602 (value Conditional.n5_140 offset) := by
  have hr : lookup Conditional.roots 133 (.leaf 0) = Conditional.n5_140 := by rfl
  simpa only [hr] using conditional_block 133 offset hoff

#print axioms conditional_at_133

theorem completed_at_134 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1041984+offset) =
      min 551 (value Completed.n5_162 offset) := by
  have hr : lookup Completed.roots 134 (.leaf 0) = Completed.n5_162 := by rfl
  simpa only [hr] using completed_block 134 offset hoff

#print axioms completed_at_134

theorem conditional_at_134 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1041984+offset) =
      min 602 (value Conditional.n5_156 offset) := by
  have hr : lookup Conditional.roots 134 (.leaf 0) = Conditional.n5_156 := by rfl
  simpa only [hr] using conditional_block 134 offset hoff

#print axioms conditional_at_134

theorem completed_at_135 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1049760+offset) =
      min 551 (value Completed.n5_66 offset) := by
  have hr : lookup Completed.roots 135 (.leaf 0) = Completed.n5_66 := by rfl
  simpa only [hr] using completed_block 135 offset hoff

#print axioms completed_at_135

theorem conditional_at_135 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1049760+offset) =
      min 602 (value Conditional.n5_71 offset) := by
  have hr : lookup Conditional.roots 135 (.leaf 0) = Conditional.n5_71 := by rfl
  simpa only [hr] using conditional_block 135 offset hoff

#print axioms conditional_at_135

theorem completed_at_136 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1057536+offset) =
      min 551 (value Completed.n5_8 offset) := by
  have hr : lookup Completed.roots 136 (.leaf 0) = Completed.n5_8 := by rfl
  simpa only [hr] using completed_block 136 offset hoff

#print axioms completed_at_136

theorem conditional_at_136 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1057536+offset) =
      min 602 (value Conditional.n5_5 offset) := by
  have hr : lookup Conditional.roots 136 (.leaf 0) = Conditional.n5_5 := by rfl
  simpa only [hr] using conditional_block 136 offset hoff

#print axioms conditional_at_136

theorem completed_at_137 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1065312+offset) =
      min 551 (value Completed.n5_125 offset) := by
  have hr : lookup Completed.roots 137 (.leaf 0) = Completed.n5_125 := by rfl
  simpa only [hr] using completed_block 137 offset hoff

#print axioms completed_at_137

theorem conditional_at_137 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1065312+offset) =
      min 602 (value Conditional.n5_120 offset) := by
  have hr : lookup Conditional.roots 137 (.leaf 0) = Conditional.n5_120 := by rfl
  simpa only [hr] using conditional_block 137 offset hoff

#print axioms conditional_at_137

theorem completed_at_138 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1073088+offset) =
      min 551 (value Completed.n5_33 offset) := by
  have hr : lookup Completed.roots 138 (.leaf 0) = Completed.n5_33 := by rfl
  simpa only [hr] using completed_block 138 offset hoff

#print axioms completed_at_138

theorem conditional_at_138 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1073088+offset) =
      min 602 (value Conditional.n5_26 offset) := by
  have hr : lookup Conditional.roots 138 (.leaf 0) = Conditional.n5_26 := by rfl
  simpa only [hr] using conditional_block 138 offset hoff

#print axioms conditional_at_138

theorem completed_at_139 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1080864+offset) =
      min 551 (value Completed.n5_57 offset) := by
  have hr : lookup Completed.roots 139 (.leaf 0) = Completed.n5_57 := by rfl
  simpa only [hr] using completed_block 139 offset hoff

#print axioms completed_at_139

theorem conditional_at_139 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1080864+offset) =
      min 602 (value Conditional.n5_52 offset) := by
  have hr : lookup Conditional.roots 139 (.leaf 0) = Conditional.n5_52 := by rfl
  simpa only [hr] using conditional_block 139 offset hoff

#print axioms conditional_at_139

theorem completed_at_140 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1088640+offset) =
      min 551 (value Completed.n5_167 offset) := by
  have hr : lookup Completed.roots 140 (.leaf 0) = Completed.n5_167 := by rfl
  simpa only [hr] using completed_block 140 offset hoff

#print axioms completed_at_140

theorem conditional_at_140 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1088640+offset) =
      min 602 (value Conditional.n5_162 offset) := by
  have hr : lookup Conditional.roots 140 (.leaf 0) = Conditional.n5_162 := by rfl
  simpa only [hr] using conditional_block 140 offset hoff

#print axioms conditional_at_140

theorem completed_at_141 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1096416+offset) =
      min 551 (value Completed.n5_154 offset) := by
  have hr : lookup Completed.roots 141 (.leaf 0) = Completed.n5_154 := by rfl
  simpa only [hr] using completed_block 141 offset hoff

#print axioms completed_at_141

theorem conditional_at_141 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1096416+offset) =
      min 602 (value Conditional.n5_148 offset) := by
  have hr : lookup Conditional.roots 141 (.leaf 0) = Conditional.n5_148 := by rfl
  simpa only [hr] using conditional_block 141 offset hoff

#print axioms conditional_at_141

theorem completed_at_142 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1104192+offset) =
      min 551 (value Completed.n5_105 offset) := by
  have hr : lookup Completed.roots 142 (.leaf 0) = Completed.n5_105 := by rfl
  simpa only [hr] using completed_block 142 offset hoff

#print axioms completed_at_142

theorem conditional_at_142 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1104192+offset) =
      min 602 (value Conditional.n5_97 offset) := by
  have hr : lookup Conditional.roots 142 (.leaf 0) = Conditional.n5_97 := by rfl
  simpa only [hr] using conditional_block 142 offset hoff

#print axioms conditional_at_142

theorem completed_at_143 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1111968+offset) =
      min 551 (value Completed.n5_152 offset) := by
  have hr : lookup Completed.roots 143 (.leaf 0) = Completed.n5_152 := by rfl
  simpa only [hr] using completed_block 143 offset hoff

#print axioms completed_at_143

theorem conditional_at_143 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1111968+offset) =
      min 602 (value Conditional.n5_146 offset) := by
  have hr : lookup Conditional.roots 143 (.leaf 0) = Conditional.n5_146 := by rfl
  simpa only [hr] using conditional_block 143 offset hoff

#print axioms conditional_at_143

theorem completed_at_144 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1119744+offset) =
      min 551 (value Completed.n5_64 offset) := by
  have hr : lookup Completed.roots 144 (.leaf 0) = Completed.n5_64 := by rfl
  simpa only [hr] using completed_block 144 offset hoff

#print axioms completed_at_144

theorem conditional_at_144 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1119744+offset) =
      min 602 (value Conditional.n5_61 offset) := by
  have hr : lookup Conditional.roots 144 (.leaf 0) = Conditional.n5_61 := by rfl
  simpa only [hr] using conditional_block 144 offset hoff

#print axioms conditional_at_144

theorem completed_at_145 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1127520+offset) =
      min 551 (value Completed.n5_51 offset) := by
  have hr : lookup Completed.roots 145 (.leaf 0) = Completed.n5_51 := by rfl
  simpa only [hr] using completed_block 145 offset hoff

#print axioms completed_at_145

theorem conditional_at_145 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1127520+offset) =
      min 602 (value Conditional.n5_50 offset) := by
  have hr : lookup Conditional.roots 145 (.leaf 0) = Conditional.n5_50 := by rfl
  simpa only [hr] using conditional_block 145 offset hoff

#print axioms conditional_at_145

theorem completed_at_146 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1135296+offset) =
      min 551 (value Completed.n5_64 offset) := by
  have hr : lookup Completed.roots 146 (.leaf 0) = Completed.n5_64 := by rfl
  simpa only [hr] using completed_block 146 offset hoff

#print axioms completed_at_146

theorem conditional_at_146 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1135296+offset) =
      min 602 (value Conditional.n5_61 offset) := by
  have hr : lookup Conditional.roots 146 (.leaf 0) = Conditional.n5_61 := by rfl
  simpa only [hr] using conditional_block 146 offset hoff

#print axioms conditional_at_146

theorem completed_at_147 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1143072+offset) =
      min 551 (value Completed.n5_88 offset) := by
  have hr : lookup Completed.roots 147 (.leaf 0) = Completed.n5_88 := by rfl
  simpa only [hr] using completed_block 147 offset hoff

#print axioms completed_at_147

theorem conditional_at_147 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1143072+offset) =
      min 602 (value Conditional.n5_91 offset) := by
  have hr : lookup Conditional.roots 147 (.leaf 0) = Conditional.n5_91 := by rfl
  simpa only [hr] using conditional_block 147 offset hoff

#print axioms conditional_at_147

theorem completed_at_148 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1150848+offset) =
      min 551 (value Completed.n5_61 offset) := by
  have hr : lookup Completed.roots 148 (.leaf 0) = Completed.n5_61 := by rfl
  simpa only [hr] using completed_block 148 offset hoff

#print axioms completed_at_148

theorem conditional_at_148 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1150848+offset) =
      min 602 (value Conditional.n5_60 offset) := by
  have hr : lookup Conditional.roots 148 (.leaf 0) = Conditional.n5_60 := by rfl
  simpa only [hr] using conditional_block 148 offset hoff

#print axioms conditional_at_148

theorem completed_at_149 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1158624+offset) =
      min 551 (value Completed.n5_45 offset) := by
  have hr : lookup Completed.roots 149 (.leaf 0) = Completed.n5_45 := by rfl
  simpa only [hr] using completed_block 149 offset hoff

#print axioms completed_at_149

theorem conditional_at_149 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1158624+offset) =
      min 602 (value Conditional.n5_45 offset) := by
  have hr : lookup Conditional.roots 149 (.leaf 0) = Conditional.n5_45 := by rfl
  simpa only [hr] using conditional_block 149 offset hoff

#print axioms conditional_at_149

theorem completed_at_150 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1166400+offset) =
      min 551 (value Completed.n5_9 offset) := by
  have hr : lookup Completed.roots 150 (.leaf 0) = Completed.n5_9 := by rfl
  simpa only [hr] using completed_block 150 offset hoff

#print axioms completed_at_150

theorem conditional_at_150 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1166400+offset) =
      min 602 (value Conditional.n5_9 offset) := by
  have hr : lookup Conditional.roots 150 (.leaf 0) = Conditional.n5_9 := by rfl
  simpa only [hr] using conditional_block 150 offset hoff

#print axioms conditional_at_150

theorem completed_at_151 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1174176+offset) =
      min 551 (value Completed.n5_15 offset) := by
  have hr : lookup Completed.roots 151 (.leaf 0) = Completed.n5_15 := by rfl
  simpa only [hr] using completed_block 151 offset hoff

#print axioms completed_at_151

theorem conditional_at_151 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1174176+offset) =
      min 602 (value Conditional.n5_16 offset) := by
  have hr : lookup Conditional.roots 151 (.leaf 0) = Conditional.n5_16 := by rfl
  simpa only [hr] using conditional_block 151 offset hoff

#print axioms conditional_at_151

theorem completed_at_152 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1181952+offset) =
      min 551 (value Completed.n5_175 offset) := by
  have hr : lookup Completed.roots 152 (.leaf 0) = Completed.n5_175 := by rfl
  simpa only [hr] using completed_block 152 offset hoff

#print axioms completed_at_152

theorem conditional_at_152 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1181952+offset) =
      min 602 (value Conditional.n5_169 offset) := by
  have hr : lookup Conditional.roots 152 (.leaf 0) = Conditional.n5_169 := by rfl
  simpa only [hr] using conditional_block 152 offset hoff

#print axioms conditional_at_152

theorem completed_at_153 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1189728+offset) =
      min 551 (value Completed.n5_142 offset) := by
  have hr : lookup Completed.roots 153 (.leaf 0) = Completed.n5_142 := by rfl
  simpa only [hr] using completed_block 153 offset hoff

#print axioms completed_at_153

theorem conditional_at_153 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1189728+offset) =
      min 602 (value Conditional.n5_137 offset) := by
  have hr : lookup Conditional.roots 153 (.leaf 0) = Conditional.n5_137 := by rfl
  simpa only [hr] using conditional_block 153 offset hoff

#print axioms conditional_at_153

theorem completed_at_154 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1197504+offset) =
      min 551 (value Completed.n5_169 offset) := by
  have hr : lookup Completed.roots 154 (.leaf 0) = Completed.n5_169 := by rfl
  simpa only [hr] using completed_block 154 offset hoff

#print axioms completed_at_154

theorem conditional_at_154 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1197504+offset) =
      min 602 (value Conditional.n5_159 offset) := by
  have hr : lookup Conditional.roots 154 (.leaf 0) = Conditional.n5_159 := by rfl
  simpa only [hr] using conditional_block 154 offset hoff

#print axioms conditional_at_154

theorem completed_at_155 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1205280+offset) =
      min 551 (value Completed.n5_155 offset) := by
  have hr : lookup Completed.roots 155 (.leaf 0) = Completed.n5_155 := by rfl
  simpa only [hr] using completed_block 155 offset hoff

#print axioms completed_at_155

theorem conditional_at_155 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1205280+offset) =
      min 602 (value Conditional.n5_149 offset) := by
  have hr : lookup Conditional.roots 155 (.leaf 0) = Conditional.n5_149 := by rfl
  simpa only [hr] using conditional_block 155 offset hoff

#print axioms conditional_at_155

end Snake9.PotentialBlocks102
