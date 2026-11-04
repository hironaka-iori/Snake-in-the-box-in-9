import ReplayCheck161_01184
import ReplayCheck161_01188
import ReplayCheck161_01192
import ReplayCheck161_01196
import ReplayCheck161_01200
import ReplayCheck161_01204
import ReplayCheck161_01208
import ReplayCheck161_01212
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps37 (τ : Nat → Bool) (h1184 : TreeTrue τ start1184) : TreeTrue τ start1216 := by
  have h1185 : TreeTrue τ start1185 := replay_true τ ok1184 h1184
  have h1186 : TreeTrue τ start1186 := replay_true τ ok1185 h1185
  have h1187 : TreeTrue τ start1187 := replay_true τ ok1186 h1186
  have h1188 : TreeTrue τ start1188 := replay_true τ ok1187 h1187
  have h1189 : TreeTrue τ start1189 := replay_true τ ok1188 h1188
  have h1190 : TreeTrue τ start1190 := replay_true τ ok1189 h1189
  have h1191 : TreeTrue τ start1191 := replay_true τ ok1190 h1190
  have h1192 : TreeTrue τ start1192 := replay_true τ ok1191 h1191
  have h1193 : TreeTrue τ start1193 := replay_true τ ok1192 h1192
  have h1194 : TreeTrue τ start1194 := replay_true τ ok1193 h1193
  have h1195 : TreeTrue τ start1195 := replay_true τ ok1194 h1194
  have h1196 : TreeTrue τ start1196 := replay_true τ ok1195 h1195
  have h1197 : TreeTrue τ start1197 := replay_true τ ok1196 h1196
  have h1198 : TreeTrue τ start1198 := replay_true τ ok1197 h1197
  have h1199 : TreeTrue τ start1199 := replay_true τ ok1198 h1198
  have h1200 : TreeTrue τ start1200 := replay_true τ ok1199 h1199
  have h1201 : TreeTrue τ start1201 := replay_true τ ok1200 h1200
  have h1202 : TreeTrue τ start1202 := replay_true τ ok1201 h1201
  have h1203 : TreeTrue τ start1203 := replay_true τ ok1202 h1202
  have h1204 : TreeTrue τ start1204 := replay_true τ ok1203 h1203
  have h1205 : TreeTrue τ start1205 := replay_true τ ok1204 h1204
  have h1206 : TreeTrue τ start1206 := replay_true τ ok1205 h1205
  have h1207 : TreeTrue τ start1207 := replay_true τ ok1206 h1206
  have h1208 : TreeTrue τ start1208 := replay_true τ ok1207 h1207
  have h1209 : TreeTrue τ start1209 := replay_true τ ok1208 h1208
  have h1210 : TreeTrue τ start1210 := replay_true τ ok1209 h1209
  have h1211 : TreeTrue τ start1211 := replay_true τ ok1210 h1210
  have h1212 : TreeTrue τ start1212 := replay_true τ ok1211 h1211
  have h1213 : TreeTrue τ start1213 := replay_true τ ok1212 h1212
  have h1214 : TreeTrue τ start1214 := replay_true τ ok1213 h1213
  have h1215 : TreeTrue τ start1215 := replay_true τ ok1214 h1214
  have h1216 : TreeTrue τ start1216 := cp_true τ ok1215 h1215
  exact h1216
#print axioms steps37
end Snake9.ReplayFull161
