import ReplayCheck161_01152
import ReplayCheck161_01156
import ReplayCheck161_01160
import ReplayCheck161_01164
import ReplayCheck161_01168
import ReplayCheck161_01172
import ReplayCheck161_01176
import ReplayCheck161_01180
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps36 (τ : Nat → Bool) (h1152 : TreeTrue τ start1152) : TreeTrue τ start1184 := by
  have h1153 : TreeTrue τ start1153 := replay_true τ ok1152 h1152
  have h1154 : TreeTrue τ start1154 := replay_true τ ok1153 h1153
  have h1155 : TreeTrue τ start1155 := replay_true τ ok1154 h1154
  have h1156 : TreeTrue τ start1156 := replay_true τ ok1155 h1155
  have h1157 : TreeTrue τ start1157 := replay_true τ ok1156 h1156
  have h1158 : TreeTrue τ start1158 := replay_true τ ok1157 h1157
  have h1159 : TreeTrue τ start1159 := replay_true τ ok1158 h1158
  have h1160 : TreeTrue τ start1160 := replay_true τ ok1159 h1159
  have h1161 : TreeTrue τ start1161 := replay_true τ ok1160 h1160
  have h1162 : TreeTrue τ start1162 := replay_true τ ok1161 h1161
  have h1163 : TreeTrue τ start1163 := replay_true τ ok1162 h1162
  have h1164 : TreeTrue τ start1164 := replay_true τ ok1163 h1163
  have h1165 : TreeTrue τ start1165 := replay_true τ ok1164 h1164
  have h1166 : TreeTrue τ start1166 := replay_true τ ok1165 h1165
  have h1167 : TreeTrue τ start1167 := replay_true τ ok1166 h1166
  have h1168 : TreeTrue τ start1168 := replay_true τ ok1167 h1167
  have h1169 : TreeTrue τ start1169 := replay_true τ ok1168 h1168
  have h1170 : TreeTrue τ start1170 := replay_true τ ok1169 h1169
  have h1171 : TreeTrue τ start1171 := replay_true τ ok1170 h1170
  have h1172 : TreeTrue τ start1172 := replay_true τ ok1171 h1171
  have h1173 : TreeTrue τ start1173 := replay_true τ ok1172 h1172
  have h1174 : TreeTrue τ start1174 := replay_true τ ok1173 h1173
  have h1175 : TreeTrue τ start1175 := replay_true τ ok1174 h1174
  have h1176 : TreeTrue τ start1176 := replay_true τ ok1175 h1175
  have h1177 : TreeTrue τ start1177 := replay_true τ ok1176 h1176
  have h1178 : TreeTrue τ start1178 := replay_true τ ok1177 h1177
  have h1179 : TreeTrue τ start1179 := replay_true τ ok1178 h1178
  have h1180 : TreeTrue τ start1180 := replay_true τ ok1179 h1179
  have h1181 : TreeTrue τ start1181 := replay_true τ ok1180 h1180
  have h1182 : TreeTrue τ start1182 := replay_true τ ok1181 h1181
  have h1183 : TreeTrue τ start1183 := replay_true τ ok1182 h1182
  have h1184 : TreeTrue τ start1184 := cp_true τ ok1183 h1183
  exact h1184
#print axioms steps36
end Snake9.ReplayFull161
