import ReplayCheck153_00000
import ReplayCheck153_00004
import ReplayCheck153_00008
import ReplayCheck153_00012
import ReplayCheck153_00016
import ReplayCheck153_00020
import ReplayCheck153_00024
import ReplayCheck153_00028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (TreeTrue)
open Snake9.LratFast153Replay
theorem steps0 (τ : Nat → Bool) (h0 : TreeTrue τ start0) : TreeTrue τ start32 := by
  have h1 : TreeTrue τ start1 := replay_true τ ok0 h0
  have h2 : TreeTrue τ start2 := replay_true τ ok1 h1
  have h3 : TreeTrue τ start3 := replay_true τ ok2 h2
  have h4 : TreeTrue τ start4 := replay_true τ ok3 h3
  have h5 : TreeTrue τ start5 := replay_true τ ok4 h4
  have h6 : TreeTrue τ start6 := replay_true τ ok5 h5
  have h7 : TreeTrue τ start7 := replay_true τ ok6 h6
  have h8 : TreeTrue τ start8 := replay_true τ ok7 h7
  have h9 : TreeTrue τ start9 := replay_true τ ok8 h8
  have h10 : TreeTrue τ start10 := replay_true τ ok9 h9
  have h11 : TreeTrue τ start11 := replay_true τ ok10 h10
  have h12 : TreeTrue τ start12 := replay_true τ ok11 h11
  have h13 : TreeTrue τ start13 := replay_true τ ok12 h12
  have h14 : TreeTrue τ start14 := replay_true τ ok13 h13
  have h15 : TreeTrue τ start15 := replay_true τ ok14 h14
  have h16 : TreeTrue τ start16 := replay_true τ ok15 h15
  have h17 : TreeTrue τ start17 := replay_true τ ok16 h16
  have h18 : TreeTrue τ start18 := replay_true τ ok17 h17
  have h19 : TreeTrue τ start19 := replay_true τ ok18 h18
  have h20 : TreeTrue τ start20 := replay_true τ ok19 h19
  have h21 : TreeTrue τ start21 := replay_true τ ok20 h20
  have h22 : TreeTrue τ start22 := replay_true τ ok21 h21
  have h23 : TreeTrue τ start23 := replay_true τ ok22 h22
  have h24 : TreeTrue τ start24 := replay_true τ ok23 h23
  have h25 : TreeTrue τ start25 := replay_true τ ok24 h24
  have h26 : TreeTrue τ start26 := replay_true τ ok25 h25
  have h27 : TreeTrue τ start27 := replay_true τ ok26 h26
  have h28 : TreeTrue τ start28 := replay_true τ ok27 h27
  have h29 : TreeTrue τ start29 := replay_true τ ok28 h28
  have h30 : TreeTrue τ start30 := replay_true τ ok29 h29
  have h31 : TreeTrue τ start31 := replay_true τ ok30 h30
  have h32 : TreeTrue τ start32 := cp_true τ ok31 h31
  exact h32
#print axioms steps0
end Snake9.ReplayFull153
