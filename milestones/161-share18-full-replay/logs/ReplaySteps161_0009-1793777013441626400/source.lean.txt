import ReplayCheck161_00288
import ReplayCheck161_00292
import ReplayCheck161_00296
import ReplayCheck161_00300
import ReplayCheck161_00304
import ReplayCheck161_00308
import ReplayCheck161_00312
import ReplayCheck161_00316
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps9 (τ : Nat → Bool) (h288 : TreeTrue τ start288) : TreeTrue τ start320 := by
  have h289 : TreeTrue τ start289 := replay_true τ ok288 h288
  have h290 : TreeTrue τ start290 := replay_true τ ok289 h289
  have h291 : TreeTrue τ start291 := replay_true τ ok290 h290
  have h292 : TreeTrue τ start292 := replay_true τ ok291 h291
  have h293 : TreeTrue τ start293 := replay_true τ ok292 h292
  have h294 : TreeTrue τ start294 := replay_true τ ok293 h293
  have h295 : TreeTrue τ start295 := replay_true τ ok294 h294
  have h296 : TreeTrue τ start296 := replay_true τ ok295 h295
  have h297 : TreeTrue τ start297 := replay_true τ ok296 h296
  have h298 : TreeTrue τ start298 := replay_true τ ok297 h297
  have h299 : TreeTrue τ start299 := replay_true τ ok298 h298
  have h300 : TreeTrue τ start300 := replay_true τ ok299 h299
  have h301 : TreeTrue τ start301 := replay_true τ ok300 h300
  have h302 : TreeTrue τ start302 := replay_true τ ok301 h301
  have h303 : TreeTrue τ start303 := replay_true τ ok302 h302
  have h304 : TreeTrue τ start304 := replay_true τ ok303 h303
  have h305 : TreeTrue τ start305 := replay_true τ ok304 h304
  have h306 : TreeTrue τ start306 := replay_true τ ok305 h305
  have h307 : TreeTrue τ start307 := replay_true τ ok306 h306
  have h308 : TreeTrue τ start308 := replay_true τ ok307 h307
  have h309 : TreeTrue τ start309 := replay_true τ ok308 h308
  have h310 : TreeTrue τ start310 := replay_true τ ok309 h309
  have h311 : TreeTrue τ start311 := replay_true τ ok310 h310
  have h312 : TreeTrue τ start312 := replay_true τ ok311 h311
  have h313 : TreeTrue τ start313 := replay_true τ ok312 h312
  have h314 : TreeTrue τ start314 := replay_true τ ok313 h313
  have h315 : TreeTrue τ start315 := replay_true τ ok314 h314
  have h316 : TreeTrue τ start316 := replay_true τ ok315 h315
  have h317 : TreeTrue τ start317 := replay_true τ ok316 h316
  have h318 : TreeTrue τ start318 := replay_true τ ok317 h317
  have h319 : TreeTrue τ start319 := replay_true τ ok318 h318
  have h320 : TreeTrue τ start320 := cp_true τ ok319 h319
  exact h320
#print axioms steps9
end Snake9.ReplayFull161
