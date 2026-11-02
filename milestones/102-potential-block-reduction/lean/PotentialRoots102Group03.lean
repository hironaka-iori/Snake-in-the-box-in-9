import PotentialBlocks102

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.PotentialBlocks102
open Snake9.Potential99 Snake9.Balanced89

theorem completed_at_156 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1213056+offset) =
      min 551 (value Completed.n5_44 offset) := by
  have hr : lookup Completed.roots 156 (.leaf 0) = Completed.n5_44 := by rfl
  simpa only [hr] using completed_block 156 offset hoff

#print axioms completed_at_156

theorem conditional_at_156 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1213056+offset) =
      min 602 (value Conditional.n5_30 offset) := by
  have hr : lookup Conditional.roots 156 (.leaf 0) = Conditional.n5_30 := by rfl
  simpa only [hr] using conditional_block 156 offset hoff

#print axioms conditional_at_156

theorem completed_at_157 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1220832+offset) =
      min 551 (value Completed.n5_59 offset) := by
  have hr : lookup Completed.roots 157 (.leaf 0) = Completed.n5_59 := by rfl
  simpa only [hr] using completed_block 157 offset hoff

#print axioms completed_at_157

theorem conditional_at_157 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1220832+offset) =
      min 602 (value Conditional.n5_57 offset) := by
  have hr : lookup Conditional.roots 157 (.leaf 0) = Conditional.n5_57 := by rfl
  simpa only [hr] using conditional_block 157 offset hoff

#print axioms conditional_at_157

theorem completed_at_158 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1228608+offset) =
      min 551 (value Completed.n5_1 offset) := by
  have hr : lookup Completed.roots 158 (.leaf 0) = Completed.n5_1 := by rfl
  simpa only [hr] using completed_block 158 offset hoff

#print axioms completed_at_158

theorem conditional_at_158 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1228608+offset) =
      min 602 (value Conditional.n5_2 offset) := by
  have hr : lookup Conditional.roots 158 (.leaf 0) = Conditional.n5_2 := by rfl
  simpa only [hr] using conditional_block 158 offset hoff

#print axioms conditional_at_158

theorem completed_at_159 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1236384+offset) =
      min 551 (value Completed.n5_84 offset) := by
  have hr : lookup Completed.roots 159 (.leaf 0) = Completed.n5_84 := by rfl
  simpa only [hr] using completed_block 159 offset hoff

#print axioms completed_at_159

theorem conditional_at_159 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1236384+offset) =
      min 602 (value Conditional.n5_79 offset) := by
  have hr : lookup Conditional.roots 159 (.leaf 0) = Conditional.n5_79 := by rfl
  simpa only [hr] using conditional_block 159 offset hoff

#print axioms conditional_at_159

theorem completed_at_160 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1244160+offset) =
      min 551 (value Completed.n5_85 offset) := by
  have hr : lookup Completed.roots 160 (.leaf 0) = Completed.n5_85 := by rfl
  simpa only [hr] using completed_block 160 offset hoff

#print axioms completed_at_160

theorem conditional_at_160 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1244160+offset) =
      min 602 (value Conditional.n5_78 offset) := by
  have hr : lookup Conditional.roots 160 (.leaf 0) = Conditional.n5_78 := by rfl
  simpa only [hr] using conditional_block 160 offset hoff

#print axioms conditional_at_160

theorem completed_at_161 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1251936+offset) =
      min 551 (value Completed.n5_62 offset) := by
  have hr : lookup Completed.roots 161 (.leaf 0) = Completed.n5_62 := by rfl
  simpa only [hr] using completed_block 161 offset hoff

#print axioms completed_at_161

theorem conditional_at_161 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1251936+offset) =
      min 602 (value Conditional.n5_56 offset) := by
  have hr : lookup Conditional.roots 161 (.leaf 0) = Conditional.n5_56 := by rfl
  simpa only [hr] using conditional_block 161 offset hoff

#print axioms conditional_at_161

theorem completed_at_162 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1259712+offset) =
      min 551 (value Completed.n5_43 offset) := by
  have hr : lookup Completed.roots 162 (.leaf 0) = Completed.n5_43 := by rfl
  simpa only [hr] using completed_block 162 offset hoff

#print axioms completed_at_162

theorem conditional_at_162 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1259712+offset) =
      min 602 (value Conditional.n5_30 offset) := by
  have hr : lookup Conditional.roots 162 (.leaf 0) = Conditional.n5_30 := by rfl
  simpa only [hr] using conditional_block 162 offset hoff

#print axioms conditional_at_162

theorem completed_at_163 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1267488+offset) =
      min 551 (value Completed.n5_60 offset) := by
  have hr : lookup Completed.roots 163 (.leaf 0) = Completed.n5_60 := by rfl
  simpa only [hr] using completed_block 163 offset hoff

#print axioms completed_at_163

theorem conditional_at_163 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1267488+offset) =
      min 602 (value Conditional.n5_58 offset) := by
  have hr : lookup Conditional.roots 163 (.leaf 0) = Conditional.n5_58 := by rfl
  simpa only [hr] using conditional_block 163 offset hoff

#print axioms conditional_at_163

theorem completed_at_164 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1275264+offset) =
      min 551 (value Completed.n5_40 offset) := by
  have hr : lookup Completed.roots 164 (.leaf 0) = Completed.n5_40 := by rfl
  simpa only [hr] using completed_block 164 offset hoff

#print axioms completed_at_164

theorem conditional_at_164 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1275264+offset) =
      min 602 (value Conditional.n5_32 offset) := by
  have hr : lookup Conditional.roots 164 (.leaf 0) = Conditional.n5_32 := by rfl
  simpa only [hr] using conditional_block 164 offset hoff

#print axioms conditional_at_164

theorem completed_at_165 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1283040+offset) =
      min 551 (value Completed.n5_60 offset) := by
  have hr : lookup Completed.roots 165 (.leaf 0) = Completed.n5_60 := by rfl
  simpa only [hr] using completed_block 165 offset hoff

#print axioms completed_at_165

theorem conditional_at_165 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1283040+offset) =
      min 602 (value Conditional.n5_58 offset) := by
  have hr : lookup Conditional.roots 165 (.leaf 0) = Conditional.n5_58 := by rfl
  simpa only [hr] using conditional_block 165 offset hoff

#print axioms conditional_at_165

theorem completed_at_166 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1290816+offset) =
      min 551 (value Completed.n5_157 offset) := by
  have hr : lookup Completed.roots 166 (.leaf 0) = Completed.n5_157 := by rfl
  simpa only [hr] using completed_block 166 offset hoff

#print axioms completed_at_166

theorem conditional_at_166 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1290816+offset) =
      min 602 (value Conditional.n5_152 offset) := by
  have hr : lookup Conditional.roots 166 (.leaf 0) = Conditional.n5_152 := by rfl
  simpa only [hr] using conditional_block 166 offset hoff

#print axioms conditional_at_166

theorem completed_at_167 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1298592+offset) =
      min 551 (value Completed.n5_144 offset) := by
  have hr : lookup Completed.roots 167 (.leaf 0) = Completed.n5_144 := by rfl
  simpa only [hr] using completed_block 167 offset hoff

#print axioms completed_at_167

theorem conditional_at_167 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1298592+offset) =
      min 602 (value Conditional.n5_138 offset) := by
  have hr : lookup Conditional.roots 167 (.leaf 0) = Conditional.n5_138 := by rfl
  simpa only [hr] using conditional_block 167 offset hoff

#print axioms conditional_at_167

theorem completed_at_168 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1306368+offset) =
      min 551 (value Completed.n5_19 offset) := by
  have hr : lookup Completed.roots 168 (.leaf 0) = Completed.n5_19 := by rfl
  simpa only [hr] using completed_block 168 offset hoff

#print axioms completed_at_168

theorem conditional_at_168 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1306368+offset) =
      min 602 (value Conditional.n5_17 offset) := by
  have hr : lookup Conditional.roots 168 (.leaf 0) = Conditional.n5_17 := by rfl
  simpa only [hr] using conditional_block 168 offset hoff

#print axioms conditional_at_168

theorem completed_at_169 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1314144+offset) =
      min 551 (value Completed.n5_3 offset) := by
  have hr : lookup Completed.roots 169 (.leaf 0) = Completed.n5_3 := by rfl
  simpa only [hr] using completed_block 169 offset hoff

#print axioms completed_at_169

theorem conditional_at_169 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1314144+offset) =
      min 602 (value Conditional.n5_4 offset) := by
  have hr : lookup Conditional.roots 169 (.leaf 0) = Conditional.n5_4 := by rfl
  simpa only [hr] using conditional_block 169 offset hoff

#print axioms conditional_at_169

theorem completed_at_170 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1321920+offset) =
      min 551 (value Completed.n5_3 offset) := by
  have hr : lookup Completed.roots 170 (.leaf 0) = Completed.n5_3 := by rfl
  simpa only [hr] using completed_block 170 offset hoff

#print axioms completed_at_170

theorem conditional_at_170 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1321920+offset) =
      min 602 (value Conditional.n5_4 offset) := by
  have hr : lookup Conditional.roots 170 (.leaf 0) = Conditional.n5_4 := by rfl
  simpa only [hr] using conditional_block 170 offset hoff

#print axioms conditional_at_170

theorem completed_at_171 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1329696+offset) =
      min 551 (value Completed.n5_166 offset) := by
  have hr : lookup Completed.roots 171 (.leaf 0) = Completed.n5_166 := by rfl
  simpa only [hr] using completed_block 171 offset hoff

#print axioms completed_at_171

theorem conditional_at_171 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1329696+offset) =
      min 602 (value Conditional.n5_161 offset) := by
  have hr : lookup Conditional.roots 171 (.leaf 0) = Conditional.n5_161 := by rfl
  simpa only [hr] using conditional_block 171 offset hoff

#print axioms conditional_at_171

theorem completed_at_172 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1337472+offset) =
      min 551 (value Completed.n5_153 offset) := by
  have hr : lookup Completed.roots 172 (.leaf 0) = Completed.n5_153 := by rfl
  simpa only [hr] using completed_block 172 offset hoff

#print axioms completed_at_172

theorem conditional_at_172 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1337472+offset) =
      min 602 (value Conditional.n5_147 offset) := by
  have hr : lookup Conditional.roots 172 (.leaf 0) = Conditional.n5_147 := by rfl
  simpa only [hr] using conditional_block 172 offset hoff

#print axioms conditional_at_172

theorem completed_at_173 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1345248+offset) =
      min 551 (value Completed.n5_161 offset) := by
  have hr : lookup Completed.roots 173 (.leaf 0) = Completed.n5_161 := by rfl
  simpa only [hr] using completed_block 173 offset hoff

#print axioms completed_at_173

theorem conditional_at_173 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1345248+offset) =
      min 602 (value Conditional.n5_153 offset) := by
  have hr : lookup Conditional.roots 173 (.leaf 0) = Conditional.n5_153 := by rfl
  simpa only [hr] using conditional_block 173 offset hoff

#print axioms conditional_at_173

theorem completed_at_174 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1353024+offset) =
      min 551 (value Completed.n5_170 offset) := by
  have hr : lookup Completed.roots 174 (.leaf 0) = Completed.n5_170 := by rfl
  simpa only [hr] using completed_block 174 offset hoff

#print axioms completed_at_174

theorem conditional_at_174 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1353024+offset) =
      min 602 (value Conditional.n5_160 offset) := by
  have hr : lookup Conditional.roots 174 (.leaf 0) = Conditional.n5_160 := by rfl
  simpa only [hr] using conditional_block 174 offset hoff

#print axioms conditional_at_174

theorem completed_at_175 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1360800+offset) =
      min 551 (value Completed.n5_92 offset) := by
  have hr : lookup Completed.roots 175 (.leaf 0) = Completed.n5_92 := by rfl
  simpa only [hr] using completed_block 175 offset hoff

#print axioms completed_at_175

theorem conditional_at_175 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1360800+offset) =
      min 602 (value Conditional.n5_88 offset) := by
  have hr : lookup Conditional.roots 175 (.leaf 0) = Conditional.n5_88 := by rfl
  simpa only [hr] using conditional_block 175 offset hoff

#print axioms conditional_at_175

theorem completed_at_176 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1368576+offset) =
      min 551 (value Completed.n5_69 offset) := by
  have hr : lookup Completed.roots 176 (.leaf 0) = Completed.n5_69 := by rfl
  simpa only [hr] using completed_block 176 offset hoff

#print axioms completed_at_176

theorem conditional_at_176 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1368576+offset) =
      min 602 (value Conditional.n5_66 offset) := by
  have hr : lookup Conditional.roots 176 (.leaf 0) = Conditional.n5_66 := by rfl
  simpa only [hr] using conditional_block 176 offset hoff

#print axioms conditional_at_176

theorem completed_at_177 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1376352+offset) =
      min 551 (value Completed.n5_4 offset) := by
  have hr : lookup Completed.roots 177 (.leaf 0) = Completed.n5_4 := by rfl
  simpa only [hr] using completed_block 177 offset hoff

#print axioms completed_at_177

theorem conditional_at_177 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1376352+offset) =
      min 602 (value Conditional.n5_0 offset) := by
  have hr : lookup Conditional.roots 177 (.leaf 0) = Conditional.n5_0 := by rfl
  simpa only [hr] using conditional_block 177 offset hoff

#print axioms conditional_at_177

theorem completed_at_178 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1384128+offset) =
      min 551 (value Completed.n5_4 offset) := by
  have hr : lookup Completed.roots 178 (.leaf 0) = Completed.n5_4 := by rfl
  simpa only [hr] using completed_block 178 offset hoff

#print axioms completed_at_178

theorem conditional_at_178 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1384128+offset) =
      min 602 (value Conditional.n5_0 offset) := by
  have hr : lookup Conditional.roots 178 (.leaf 0) = Conditional.n5_0 := by rfl
  simpa only [hr] using conditional_block 178 offset hoff

#print axioms conditional_at_178

theorem completed_at_179 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1391904+offset) =
      min 551 (value Completed.n5_31 offset) := by
  have hr : lookup Completed.roots 179 (.leaf 0) = Completed.n5_31 := by rfl
  simpa only [hr] using completed_block 179 offset hoff

#print axioms completed_at_179

theorem conditional_at_179 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1391904+offset) =
      min 602 (value Conditional.n5_35 offset) := by
  have hr : lookup Conditional.roots 179 (.leaf 0) = Conditional.n5_35 := by rfl
  simpa only [hr] using conditional_block 179 offset hoff

#print axioms conditional_at_179

theorem completed_at_180 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1399680+offset) =
      min 551 (value Completed.n5_73 offset) := by
  have hr : lookup Completed.roots 180 (.leaf 0) = Completed.n5_73 := by rfl
  simpa only [hr] using completed_block 180 offset hoff

#print axioms completed_at_180

theorem conditional_at_180 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1399680+offset) =
      min 602 (value Conditional.n5_82 offset) := by
  have hr : lookup Conditional.roots 180 (.leaf 0) = Conditional.n5_82 := by rfl
  simpa only [hr] using conditional_block 180 offset hoff

#print axioms conditional_at_180

theorem completed_at_181 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1407456+offset) =
      min 551 (value Completed.n5_73 offset) := by
  have hr : lookup Completed.roots 181 (.leaf 0) = Completed.n5_73 := by rfl
  simpa only [hr] using completed_block 181 offset hoff

#print axioms completed_at_181

theorem conditional_at_181 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1407456+offset) =
      min 602 (value Conditional.n5_82 offset) := by
  have hr : lookup Conditional.roots 181 (.leaf 0) = Conditional.n5_82 := by rfl
  simpa only [hr] using conditional_block 181 offset hoff

#print axioms conditional_at_181

theorem completed_at_182 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1415232+offset) =
      min 551 (value Completed.n5_31 offset) := by
  have hr : lookup Completed.roots 182 (.leaf 0) = Completed.n5_31 := by rfl
  simpa only [hr] using completed_block 182 offset hoff

#print axioms completed_at_182

theorem conditional_at_182 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1415232+offset) =
      min 602 (value Conditional.n5_35 offset) := by
  have hr : lookup Conditional.roots 182 (.leaf 0) = Conditional.n5_35 := by rfl
  simpa only [hr] using conditional_block 182 offset hoff

#print axioms conditional_at_182

theorem completed_at_183 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1423008+offset) =
      min 551 (value Completed.n5_158 offset) := by
  have hr : lookup Completed.roots 183 (.leaf 0) = Completed.n5_158 := by rfl
  simpa only [hr] using completed_block 183 offset hoff

#print axioms completed_at_183

theorem conditional_at_183 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1423008+offset) =
      min 602 (value Conditional.n5_154 offset) := by
  have hr : lookup Conditional.roots 183 (.leaf 0) = Conditional.n5_154 := by rfl
  simpa only [hr] using conditional_block 183 offset hoff

#print axioms conditional_at_183

theorem completed_at_184 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1430784+offset) =
      min 551 (value Completed.n5_158 offset) := by
  have hr : lookup Completed.roots 184 (.leaf 0) = Completed.n5_158 := by rfl
  simpa only [hr] using completed_block 184 offset hoff

#print axioms completed_at_184

theorem conditional_at_184 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1430784+offset) =
      min 602 (value Conditional.n5_154 offset) := by
  have hr : lookup Conditional.roots 184 (.leaf 0) = Conditional.n5_154 := by rfl
  simpa only [hr] using conditional_block 184 offset hoff

#print axioms conditional_at_184

theorem completed_at_185 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1438560+offset) =
      min 551 (value Completed.n5_47 offset) := by
  have hr : lookup Completed.roots 185 (.leaf 0) = Completed.n5_47 := by rfl
  simpa only [hr] using completed_block 185 offset hoff

#print axioms completed_at_185

theorem conditional_at_185 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1438560+offset) =
      min 602 (value Conditional.n5_47 offset) := by
  have hr : lookup Conditional.roots 185 (.leaf 0) = Conditional.n5_47 := by rfl
  simpa only [hr] using conditional_block 185 offset hoff

#print axioms conditional_at_185

theorem completed_at_186 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1446336+offset) =
      min 551 (value Completed.n5_89 offset) := by
  have hr : lookup Completed.roots 186 (.leaf 0) = Completed.n5_89 := by rfl
  simpa only [hr] using completed_block 186 offset hoff

#print axioms completed_at_186

theorem conditional_at_186 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1446336+offset) =
      min 602 (value Conditional.n5_90 offset) := by
  have hr : lookup Conditional.roots 186 (.leaf 0) = Conditional.n5_90 := by rfl
  simpa only [hr] using conditional_block 186 offset hoff

#print axioms conditional_at_186

theorem completed_at_187 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1454112+offset) =
      min 551 (value Completed.n5_32 offset) := by
  have hr : lookup Completed.roots 187 (.leaf 0) = Completed.n5_32 := by rfl
  simpa only [hr] using completed_block 187 offset hoff

#print axioms completed_at_187

theorem conditional_at_187 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1454112+offset) =
      min 602 (value Conditional.n5_25 offset) := by
  have hr : lookup Conditional.roots 187 (.leaf 0) = Conditional.n5_25 := by rfl
  simpa only [hr] using conditional_block 187 offset hoff

#print axioms conditional_at_187

theorem completed_at_188 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1461888+offset) =
      min 551 (value Completed.n5_56 offset) := by
  have hr : lookup Completed.roots 188 (.leaf 0) = Completed.n5_56 := by rfl
  simpa only [hr] using completed_block 188 offset hoff

#print axioms completed_at_188

theorem conditional_at_188 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1461888+offset) =
      min 602 (value Conditional.n5_52 offset) := by
  have hr : lookup Conditional.roots 188 (.leaf 0) = Conditional.n5_52 := by rfl
  simpa only [hr] using conditional_block 188 offset hoff

#print axioms conditional_at_188

theorem completed_at_189 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1469664+offset) =
      min 551 (value Completed.n5_115 offset) := by
  have hr : lookup Completed.roots 189 (.leaf 0) = Completed.n5_115 := by rfl
  simpa only [hr] using completed_block 189 offset hoff

#print axioms completed_at_189

theorem conditional_at_189 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1469664+offset) =
      min 602 (value Conditional.n5_87 offset) := by
  have hr : lookup Conditional.roots 189 (.leaf 0) = Conditional.n5_87 := by rfl
  simpa only [hr] using conditional_block 189 offset hoff

#print axioms conditional_at_189

theorem completed_at_190 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1477440+offset) =
      min 551 (value Completed.n5_101 offset) := by
  have hr : lookup Completed.roots 190 (.leaf 0) = Completed.n5_101 := by rfl
  simpa only [hr] using completed_block 190 offset hoff

#print axioms completed_at_190

theorem conditional_at_190 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1477440+offset) =
      min 602 (value Conditional.n5_111 offset) := by
  have hr : lookup Conditional.roots 190 (.leaf 0) = Conditional.n5_111 := by rfl
  simpa only [hr] using conditional_block 190 offset hoff

#print axioms conditional_at_190

theorem completed_at_191 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1485216+offset) =
      min 551 (value Completed.n5_49 offset) := by
  have hr : lookup Completed.roots 191 (.leaf 0) = Completed.n5_49 := by rfl
  simpa only [hr] using completed_block 191 offset hoff

#print axioms completed_at_191

theorem conditional_at_191 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1485216+offset) =
      min 602 (value Conditional.n5_49 offset) := by
  have hr : lookup Conditional.roots 191 (.leaf 0) = Conditional.n5_49 := by rfl
  simpa only [hr] using conditional_block 191 offset hoff

#print axioms conditional_at_191

theorem completed_at_192 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1492992+offset) =
      min 551 (value Completed.n5_52 offset) := by
  have hr : lookup Completed.roots 192 (.leaf 0) = Completed.n5_52 := by rfl
  simpa only [hr] using completed_block 192 offset hoff

#print axioms completed_at_192

theorem conditional_at_192 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1492992+offset) =
      min 602 (value Conditional.n5_51 offset) := by
  have hr : lookup Conditional.roots 192 (.leaf 0) = Conditional.n5_51 := by rfl
  simpa only [hr] using conditional_block 192 offset hoff

#print axioms conditional_at_192

theorem completed_at_193 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1500768+offset) =
      min 551 (value Completed.n5_151 offset) := by
  have hr : lookup Completed.roots 193 (.leaf 0) = Completed.n5_151 := by rfl
  simpa only [hr] using completed_block 193 offset hoff

#print axioms completed_at_193

theorem conditional_at_193 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1500768+offset) =
      min 602 (value Conditional.n5_144 offset) := by
  have hr : lookup Conditional.roots 193 (.leaf 0) = Conditional.n5_144 := by rfl
  simpa only [hr] using conditional_block 193 offset hoff

#print axioms conditional_at_193

theorem completed_at_194 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1508544+offset) =
      min 551 (value Completed.n5_115 offset) := by
  have hr : lookup Completed.roots 194 (.leaf 0) = Completed.n5_115 := by rfl
  simpa only [hr] using completed_block 194 offset hoff

#print axioms completed_at_194

theorem conditional_at_194 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1508544+offset) =
      min 602 (value Conditional.n5_87 offset) := by
  have hr : lookup Conditional.roots 194 (.leaf 0) = Conditional.n5_87 := by rfl
  simpa only [hr] using conditional_block 194 offset hoff

#print axioms conditional_at_194

theorem completed_at_195 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1516320+offset) =
      min 551 (value Completed.n5_101 offset) := by
  have hr : lookup Completed.roots 195 (.leaf 0) = Completed.n5_101 := by rfl
  simpa only [hr] using completed_block 195 offset hoff

#print axioms completed_at_195

theorem conditional_at_195 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1516320+offset) =
      min 602 (value Conditional.n5_111 offset) := by
  have hr : lookup Conditional.roots 195 (.leaf 0) = Conditional.n5_111 := by rfl
  simpa only [hr] using conditional_block 195 offset hoff

#print axioms conditional_at_195

theorem completed_at_196 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1524096+offset) =
      min 551 (value Completed.n5_91 offset) := by
  have hr : lookup Completed.roots 196 (.leaf 0) = Completed.n5_91 := by rfl
  simpa only [hr] using completed_block 196 offset hoff

#print axioms completed_at_196

theorem conditional_at_196 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1524096+offset) =
      min 602 (value Conditional.n5_89 offset) := by
  have hr : lookup Conditional.roots 196 (.leaf 0) = Conditional.n5_89 := by rfl
  simpa only [hr] using conditional_block 196 offset hoff

#print axioms conditional_at_196

theorem completed_at_197 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1531872+offset) =
      min 551 (value Completed.n5_46 offset) := by
  have hr : lookup Completed.roots 197 (.leaf 0) = Completed.n5_46 := by rfl
  simpa only [hr] using completed_block 197 offset hoff

#print axioms completed_at_197

theorem conditional_at_197 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1531872+offset) =
      min 602 (value Conditional.n5_48 offset) := by
  have hr : lookup Conditional.roots 197 (.leaf 0) = Conditional.n5_48 := by rfl
  simpa only [hr] using conditional_block 197 offset hoff

#print axioms conditional_at_197

theorem completed_at_198 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1539648+offset) =
      min 551 (value Completed.n5_11 offset) := by
  have hr : lookup Completed.roots 198 (.leaf 0) = Completed.n5_11 := by rfl
  simpa only [hr] using completed_block 198 offset hoff

#print axioms completed_at_198

theorem conditional_at_198 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1539648+offset) =
      min 602 (value Conditional.n5_11 offset) := by
  have hr : lookup Conditional.roots 198 (.leaf 0) = Conditional.n5_11 := by rfl
  simpa only [hr] using conditional_block 198 offset hoff

#print axioms conditional_at_198

theorem completed_at_199 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1547424+offset) =
      min 551 (value Completed.n5_159 offset) := by
  have hr : lookup Completed.roots 199 (.leaf 0) = Completed.n5_159 := by rfl
  simpa only [hr] using completed_block 199 offset hoff

#print axioms completed_at_199

theorem conditional_at_199 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1547424+offset) =
      min 602 (value Conditional.n5_151 offset) := by
  have hr : lookup Conditional.roots 199 (.leaf 0) = Conditional.n5_151 := by rfl
  simpa only [hr] using conditional_block 199 offset hoff

#print axioms conditional_at_199

theorem completed_at_200 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1555200+offset) =
      min 551 (value Completed.n5_174 offset) := by
  have hr : lookup Completed.roots 200 (.leaf 0) = Completed.n5_174 := by rfl
  simpa only [hr] using completed_block 200 offset hoff

#print axioms completed_at_200

theorem conditional_at_200 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1555200+offset) =
      min 602 (value Conditional.n5_166 offset) := by
  have hr : lookup Conditional.roots 200 (.leaf 0) = Conditional.n5_166 := by rfl
  simpa only [hr] using conditional_block 200 offset hoff

#print axioms conditional_at_200

theorem completed_at_201 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1562976+offset) =
      min 551 (value Completed.n5_164 offset) := by
  have hr : lookup Completed.roots 201 (.leaf 0) = Completed.n5_164 := by rfl
  simpa only [hr] using completed_block 201 offset hoff

#print axioms completed_at_201

theorem conditional_at_201 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1562976+offset) =
      min 602 (value Conditional.n5_158 offset) := by
  have hr : lookup Conditional.roots 201 (.leaf 0) = Conditional.n5_158 := by rfl
  simpa only [hr] using conditional_block 201 offset hoff

#print axioms conditional_at_201

theorem completed_at_202 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1570752+offset) =
      min 551 (value Completed.n5_159 offset) := by
  have hr : lookup Completed.roots 202 (.leaf 0) = Completed.n5_159 := by rfl
  simpa only [hr] using completed_block 202 offset hoff

#print axioms completed_at_202

theorem conditional_at_202 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1570752+offset) =
      min 602 (value Conditional.n5_151 offset) := by
  have hr : lookup Conditional.roots 202 (.leaf 0) = Conditional.n5_151 := by rfl
  simpa only [hr] using conditional_block 202 offset hoff

#print axioms conditional_at_202

theorem completed_at_203 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1578528+offset) =
      min 551 (value Completed.n5_164 offset) := by
  have hr : lookup Completed.roots 203 (.leaf 0) = Completed.n5_164 := by rfl
  simpa only [hr] using completed_block 203 offset hoff

#print axioms completed_at_203

theorem conditional_at_203 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1578528+offset) =
      min 602 (value Conditional.n5_158 offset) := by
  have hr : lookup Conditional.roots 203 (.leaf 0) = Conditional.n5_158 := by rfl
  simpa only [hr] using conditional_block 203 offset hoff

#print axioms conditional_at_203

theorem completed_at_204 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1586304+offset) =
      min 551 (value Completed.n5_48 offset) := by
  have hr : lookup Completed.roots 204 (.leaf 0) = Completed.n5_48 := by rfl
  simpa only [hr] using completed_block 204 offset hoff

#print axioms completed_at_204

theorem conditional_at_204 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1586304+offset) =
      min 602 (value Conditional.n5_46 offset) := by
  have hr : lookup Conditional.roots 204 (.leaf 0) = Conditional.n5_46 := by rfl
  simpa only [hr] using conditional_block 204 offset hoff

#print axioms conditional_at_204

theorem completed_at_205 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (1594080+offset) =
      min 551 (value Completed.n5_90 offset) := by
  have hr : lookup Completed.roots 205 (.leaf 0) = Completed.n5_90 := by rfl
  simpa only [hr] using completed_block 205 offset hoff

#print axioms completed_at_205

theorem conditional_at_205 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (1594080+offset) =
      min 602 (value Conditional.n5_89 offset) := by
  have hr : lookup Conditional.roots 205 (.leaf 0) = Conditional.n5_89 := by rfl
  simpa only [hr] using conditional_block 205 offset hoff

#print axioms conditional_at_205

end Snake9.PotentialBlocks102
