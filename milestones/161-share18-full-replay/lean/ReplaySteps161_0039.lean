import ReplayCheck161_01248
import ReplayCheck161_01252
import ReplayCheck161_01256
import ReplayCheck161_01260
import ReplayCheck161_01264
import ReplayCheck161_01268
import ReplayCheck161_01272
import ReplayCheck161_01276
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps39 (τ : Nat → Bool) (h1248 : TreeTrue τ start1248) : TreeTrue τ start1280 := by
  have h1249 : TreeTrue τ start1249 := replay_true τ ok1248 h1248
  have h1250 : TreeTrue τ start1250 := replay_true τ ok1249 h1249
  have h1251 : TreeTrue τ start1251 := replay_true τ ok1250 h1250
  have h1252 : TreeTrue τ start1252 := replay_true τ ok1251 h1251
  have h1253 : TreeTrue τ start1253 := replay_true τ ok1252 h1252
  have h1254 : TreeTrue τ start1254 := replay_true τ ok1253 h1253
  have h1255 : TreeTrue τ start1255 := replay_true τ ok1254 h1254
  have h1256 : TreeTrue τ start1256 := replay_true τ ok1255 h1255
  have h1257 : TreeTrue τ start1257 := replay_true τ ok1256 h1256
  have h1258 : TreeTrue τ start1258 := replay_true τ ok1257 h1257
  have h1259 : TreeTrue τ start1259 := replay_true τ ok1258 h1258
  have h1260 : TreeTrue τ start1260 := replay_true τ ok1259 h1259
  have h1261 : TreeTrue τ start1261 := replay_true τ ok1260 h1260
  have h1262 : TreeTrue τ start1262 := replay_true τ ok1261 h1261
  have h1263 : TreeTrue τ start1263 := replay_true τ ok1262 h1262
  have h1264 : TreeTrue τ start1264 := replay_true τ ok1263 h1263
  have h1265 : TreeTrue τ start1265 := replay_true τ ok1264 h1264
  have h1266 : TreeTrue τ start1266 := replay_true τ ok1265 h1265
  have h1267 : TreeTrue τ start1267 := replay_true τ ok1266 h1266
  have h1268 : TreeTrue τ start1268 := replay_true τ ok1267 h1267
  have h1269 : TreeTrue τ start1269 := replay_true τ ok1268 h1268
  have h1270 : TreeTrue τ start1270 := replay_true τ ok1269 h1269
  have h1271 : TreeTrue τ start1271 := replay_true τ ok1270 h1270
  have h1272 : TreeTrue τ start1272 := replay_true τ ok1271 h1271
  have h1273 : TreeTrue τ start1273 := replay_true τ ok1272 h1272
  have h1274 : TreeTrue τ start1274 := replay_true τ ok1273 h1273
  have h1275 : TreeTrue τ start1275 := replay_true τ ok1274 h1274
  have h1276 : TreeTrue τ start1276 := replay_true τ ok1275 h1275
  have h1277 : TreeTrue τ start1277 := replay_true τ ok1276 h1276
  have h1278 : TreeTrue τ start1278 := replay_true τ ok1277 h1277
  have h1279 : TreeTrue τ start1279 := replay_true τ ok1278 h1278
  have h1280 : TreeTrue τ start1280 := cp_true τ ok1279 h1279
  exact h1280
#print axioms steps39
end Snake9.ReplayFull161
