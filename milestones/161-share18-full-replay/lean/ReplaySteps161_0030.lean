import ReplayCheck161_00960
import ReplayCheck161_00964
import ReplayCheck161_00968
import ReplayCheck161_00972
import ReplayCheck161_00976
import ReplayCheck161_00980
import ReplayCheck161_00984
import ReplayCheck161_00988
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps30 (τ : Nat → Bool) (h960 : TreeTrue τ start960) : TreeTrue τ start992 := by
  have h961 : TreeTrue τ start961 := replay_true τ ok960 h960
  have h962 : TreeTrue τ start962 := replay_true τ ok961 h961
  have h963 : TreeTrue τ start963 := replay_true τ ok962 h962
  have h964 : TreeTrue τ start964 := replay_true τ ok963 h963
  have h965 : TreeTrue τ start965 := replay_true τ ok964 h964
  have h966 : TreeTrue τ start966 := replay_true τ ok965 h965
  have h967 : TreeTrue τ start967 := replay_true τ ok966 h966
  have h968 : TreeTrue τ start968 := replay_true τ ok967 h967
  have h969 : TreeTrue τ start969 := replay_true τ ok968 h968
  have h970 : TreeTrue τ start970 := replay_true τ ok969 h969
  have h971 : TreeTrue τ start971 := replay_true τ ok970 h970
  have h972 : TreeTrue τ start972 := replay_true τ ok971 h971
  have h973 : TreeTrue τ start973 := replay_true τ ok972 h972
  have h974 : TreeTrue τ start974 := replay_true τ ok973 h973
  have h975 : TreeTrue τ start975 := replay_true τ ok974 h974
  have h976 : TreeTrue τ start976 := replay_true τ ok975 h975
  have h977 : TreeTrue τ start977 := replay_true τ ok976 h976
  have h978 : TreeTrue τ start978 := replay_true τ ok977 h977
  have h979 : TreeTrue τ start979 := replay_true τ ok978 h978
  have h980 : TreeTrue τ start980 := replay_true τ ok979 h979
  have h981 : TreeTrue τ start981 := replay_true τ ok980 h980
  have h982 : TreeTrue τ start982 := replay_true τ ok981 h981
  have h983 : TreeTrue τ start983 := replay_true τ ok982 h982
  have h984 : TreeTrue τ start984 := replay_true τ ok983 h983
  have h985 : TreeTrue τ start985 := replay_true τ ok984 h984
  have h986 : TreeTrue τ start986 := replay_true τ ok985 h985
  have h987 : TreeTrue τ start987 := replay_true τ ok986 h986
  have h988 : TreeTrue τ start988 := replay_true τ ok987 h987
  have h989 : TreeTrue τ start989 := replay_true τ ok988 h988
  have h990 : TreeTrue τ start990 := replay_true τ ok989 h989
  have h991 : TreeTrue τ start991 := replay_true τ ok990 h990
  have h992 : TreeTrue τ start992 := cp_true τ ok991 h991
  exact h992
#print axioms steps30
end Snake9.ReplayFull161
