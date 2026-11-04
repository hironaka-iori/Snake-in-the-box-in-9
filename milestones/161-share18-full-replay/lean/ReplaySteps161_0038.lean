import ReplayCheck161_01216
import ReplayCheck161_01220
import ReplayCheck161_01224
import ReplayCheck161_01228
import ReplayCheck161_01232
import ReplayCheck161_01236
import ReplayCheck161_01240
import ReplayCheck161_01244
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps38 (τ : Nat → Bool) (h1216 : TreeTrue τ start1216) : TreeTrue τ start1248 := by
  have h1217 : TreeTrue τ start1217 := replay_true τ ok1216 h1216
  have h1218 : TreeTrue τ start1218 := replay_true τ ok1217 h1217
  have h1219 : TreeTrue τ start1219 := replay_true τ ok1218 h1218
  have h1220 : TreeTrue τ start1220 := replay_true τ ok1219 h1219
  have h1221 : TreeTrue τ start1221 := replay_true τ ok1220 h1220
  have h1222 : TreeTrue τ start1222 := replay_true τ ok1221 h1221
  have h1223 : TreeTrue τ start1223 := replay_true τ ok1222 h1222
  have h1224 : TreeTrue τ start1224 := replay_true τ ok1223 h1223
  have h1225 : TreeTrue τ start1225 := replay_true τ ok1224 h1224
  have h1226 : TreeTrue τ start1226 := replay_true τ ok1225 h1225
  have h1227 : TreeTrue τ start1227 := replay_true τ ok1226 h1226
  have h1228 : TreeTrue τ start1228 := replay_true τ ok1227 h1227
  have h1229 : TreeTrue τ start1229 := replay_true τ ok1228 h1228
  have h1230 : TreeTrue τ start1230 := replay_true τ ok1229 h1229
  have h1231 : TreeTrue τ start1231 := replay_true τ ok1230 h1230
  have h1232 : TreeTrue τ start1232 := replay_true τ ok1231 h1231
  have h1233 : TreeTrue τ start1233 := replay_true τ ok1232 h1232
  have h1234 : TreeTrue τ start1234 := replay_true τ ok1233 h1233
  have h1235 : TreeTrue τ start1235 := replay_true τ ok1234 h1234
  have h1236 : TreeTrue τ start1236 := replay_true τ ok1235 h1235
  have h1237 : TreeTrue τ start1237 := replay_true τ ok1236 h1236
  have h1238 : TreeTrue τ start1238 := replay_true τ ok1237 h1237
  have h1239 : TreeTrue τ start1239 := replay_true τ ok1238 h1238
  have h1240 : TreeTrue τ start1240 := replay_true τ ok1239 h1239
  have h1241 : TreeTrue τ start1241 := replay_true τ ok1240 h1240
  have h1242 : TreeTrue τ start1242 := replay_true τ ok1241 h1241
  have h1243 : TreeTrue τ start1243 := replay_true τ ok1242 h1242
  have h1244 : TreeTrue τ start1244 := replay_true τ ok1243 h1243
  have h1245 : TreeTrue τ start1245 := replay_true τ ok1244 h1244
  have h1246 : TreeTrue τ start1246 := replay_true τ ok1245 h1245
  have h1247 : TreeTrue τ start1247 := replay_true τ ok1246 h1246
  have h1248 : TreeTrue τ start1248 := cp_true τ ok1247 h1247
  exact h1248
#print axioms steps38
end Snake9.ReplayFull161
