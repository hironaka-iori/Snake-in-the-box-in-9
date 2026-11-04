import ReplayCheck153_00224
import ReplayCheck153_00228
import ReplayCheck153_00232
import ReplayCheck153_00236
import ReplayCheck153_00240
import ReplayCheck153_00244
import ReplayCheck153_00248
import ReplayCheck153_00252
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (TreeTrue)
open Snake9.LratFast153Replay
theorem steps7 (τ : Nat → Bool) (h224 : TreeTrue τ start224) : TreeTrue τ start256 := by
  have h225 : TreeTrue τ start225 := replay_true τ ok224 h224
  have h226 : TreeTrue τ start226 := replay_true τ ok225 h225
  have h227 : TreeTrue τ start227 := replay_true τ ok226 h226
  have h228 : TreeTrue τ start228 := replay_true τ ok227 h227
  have h229 : TreeTrue τ start229 := replay_true τ ok228 h228
  have h230 : TreeTrue τ start230 := replay_true τ ok229 h229
  have h231 : TreeTrue τ start231 := replay_true τ ok230 h230
  have h232 : TreeTrue τ start232 := replay_true τ ok231 h231
  have h233 : TreeTrue τ start233 := replay_true τ ok232 h232
  have h234 : TreeTrue τ start234 := replay_true τ ok233 h233
  have h235 : TreeTrue τ start235 := replay_true τ ok234 h234
  have h236 : TreeTrue τ start236 := replay_true τ ok235 h235
  have h237 : TreeTrue τ start237 := replay_true τ ok236 h236
  have h238 : TreeTrue τ start238 := replay_true τ ok237 h237
  have h239 : TreeTrue τ start239 := replay_true τ ok238 h238
  have h240 : TreeTrue τ start240 := replay_true τ ok239 h239
  have h241 : TreeTrue τ start241 := replay_true τ ok240 h240
  have h242 : TreeTrue τ start242 := replay_true τ ok241 h241
  have h243 : TreeTrue τ start243 := replay_true τ ok242 h242
  have h244 : TreeTrue τ start244 := replay_true τ ok243 h243
  have h245 : TreeTrue τ start245 := replay_true τ ok244 h244
  have h246 : TreeTrue τ start246 := replay_true τ ok245 h245
  have h247 : TreeTrue τ start247 := replay_true τ ok246 h246
  have h248 : TreeTrue τ start248 := replay_true τ ok247 h247
  have h249 : TreeTrue τ start249 := replay_true τ ok248 h248
  have h250 : TreeTrue τ start250 := replay_true τ ok249 h249
  have h251 : TreeTrue τ start251 := replay_true τ ok250 h250
  have h252 : TreeTrue τ start252 := replay_true τ ok251 h251
  have h253 : TreeTrue τ start253 := replay_true τ ok252 h252
  have h254 : TreeTrue τ start254 := replay_true τ ok253 h253
  have h255 : TreeTrue τ start255 := replay_true τ ok254 h254
  have h256 : TreeTrue τ start256 := cp_true τ ok255 h255
  exact h256
#print axioms steps7
end Snake9.ReplayFull153
