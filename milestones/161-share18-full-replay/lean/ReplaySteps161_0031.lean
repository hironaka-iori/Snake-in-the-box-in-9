import ReplayCheck161_00992
import ReplayCheck161_00996
import ReplayCheck161_01000
import ReplayCheck161_01004
import ReplayCheck161_01008
import ReplayCheck161_01012
import ReplayCheck161_01016
import ReplayCheck161_01020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps31 (τ : Nat → Bool) (h992 : TreeTrue τ start992) : TreeTrue τ start1024 := by
  have h993 : TreeTrue τ start993 := replay_true τ ok992 h992
  have h994 : TreeTrue τ start994 := replay_true τ ok993 h993
  have h995 : TreeTrue τ start995 := replay_true τ ok994 h994
  have h996 : TreeTrue τ start996 := replay_true τ ok995 h995
  have h997 : TreeTrue τ start997 := replay_true τ ok996 h996
  have h998 : TreeTrue τ start998 := replay_true τ ok997 h997
  have h999 : TreeTrue τ start999 := replay_true τ ok998 h998
  have h1000 : TreeTrue τ start1000 := replay_true τ ok999 h999
  have h1001 : TreeTrue τ start1001 := replay_true τ ok1000 h1000
  have h1002 : TreeTrue τ start1002 := replay_true τ ok1001 h1001
  have h1003 : TreeTrue τ start1003 := replay_true τ ok1002 h1002
  have h1004 : TreeTrue τ start1004 := replay_true τ ok1003 h1003
  have h1005 : TreeTrue τ start1005 := replay_true τ ok1004 h1004
  have h1006 : TreeTrue τ start1006 := replay_true τ ok1005 h1005
  have h1007 : TreeTrue τ start1007 := replay_true τ ok1006 h1006
  have h1008 : TreeTrue τ start1008 := replay_true τ ok1007 h1007
  have h1009 : TreeTrue τ start1009 := replay_true τ ok1008 h1008
  have h1010 : TreeTrue τ start1010 := replay_true τ ok1009 h1009
  have h1011 : TreeTrue τ start1011 := replay_true τ ok1010 h1010
  have h1012 : TreeTrue τ start1012 := replay_true τ ok1011 h1011
  have h1013 : TreeTrue τ start1013 := replay_true τ ok1012 h1012
  have h1014 : TreeTrue τ start1014 := replay_true τ ok1013 h1013
  have h1015 : TreeTrue τ start1015 := replay_true τ ok1014 h1014
  have h1016 : TreeTrue τ start1016 := replay_true τ ok1015 h1015
  have h1017 : TreeTrue τ start1017 := replay_true τ ok1016 h1016
  have h1018 : TreeTrue τ start1018 := replay_true τ ok1017 h1017
  have h1019 : TreeTrue τ start1019 := replay_true τ ok1018 h1018
  have h1020 : TreeTrue τ start1020 := replay_true τ ok1019 h1019
  have h1021 : TreeTrue τ start1021 := replay_true τ ok1020 h1020
  have h1022 : TreeTrue τ start1022 := replay_true τ ok1021 h1021
  have h1023 : TreeTrue τ start1023 := replay_true τ ok1022 h1022
  have h1024 : TreeTrue τ start1024 := cp_true τ ok1023 h1023
  exact h1024
#print axioms steps31
end Snake9.ReplayFull161
