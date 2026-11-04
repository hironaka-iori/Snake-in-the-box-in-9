import ReplayCheck161_00320
import ReplayCheck161_00324
import ReplayCheck161_00328
import ReplayCheck161_00332
import ReplayCheck161_00336
import ReplayCheck161_00340
import ReplayCheck161_00344
import ReplayCheck161_00348
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps10 (τ : Nat → Bool) (h320 : TreeTrue τ start320) : TreeTrue τ start352 := by
  have h321 : TreeTrue τ start321 := replay_true τ ok320 h320
  have h322 : TreeTrue τ start322 := replay_true τ ok321 h321
  have h323 : TreeTrue τ start323 := replay_true τ ok322 h322
  have h324 : TreeTrue τ start324 := replay_true τ ok323 h323
  have h325 : TreeTrue τ start325 := replay_true τ ok324 h324
  have h326 : TreeTrue τ start326 := replay_true τ ok325 h325
  have h327 : TreeTrue τ start327 := replay_true τ ok326 h326
  have h328 : TreeTrue τ start328 := replay_true τ ok327 h327
  have h329 : TreeTrue τ start329 := replay_true τ ok328 h328
  have h330 : TreeTrue τ start330 := replay_true τ ok329 h329
  have h331 : TreeTrue τ start331 := replay_true τ ok330 h330
  have h332 : TreeTrue τ start332 := replay_true τ ok331 h331
  have h333 : TreeTrue τ start333 := replay_true τ ok332 h332
  have h334 : TreeTrue τ start334 := replay_true τ ok333 h333
  have h335 : TreeTrue τ start335 := replay_true τ ok334 h334
  have h336 : TreeTrue τ start336 := replay_true τ ok335 h335
  have h337 : TreeTrue τ start337 := replay_true τ ok336 h336
  have h338 : TreeTrue τ start338 := replay_true τ ok337 h337
  have h339 : TreeTrue τ start339 := replay_true τ ok338 h338
  have h340 : TreeTrue τ start340 := replay_true τ ok339 h339
  have h341 : TreeTrue τ start341 := replay_true τ ok340 h340
  have h342 : TreeTrue τ start342 := replay_true τ ok341 h341
  have h343 : TreeTrue τ start343 := replay_true τ ok342 h342
  have h344 : TreeTrue τ start344 := replay_true τ ok343 h343
  have h345 : TreeTrue τ start345 := replay_true τ ok344 h344
  have h346 : TreeTrue τ start346 := replay_true τ ok345 h345
  have h347 : TreeTrue τ start347 := replay_true τ ok346 h346
  have h348 : TreeTrue τ start348 := replay_true τ ok347 h347
  have h349 : TreeTrue τ start349 := replay_true τ ok348 h348
  have h350 : TreeTrue τ start350 := replay_true τ ok349 h349
  have h351 : TreeTrue τ start351 := replay_true τ ok350 h350
  have h352 : TreeTrue τ start352 := cp_true τ ok351 h351
  exact h352
#print axioms steps10
end Snake9.ReplayFull161
