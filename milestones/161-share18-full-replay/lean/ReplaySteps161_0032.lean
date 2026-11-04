import ReplayCheck161_01024
import ReplayCheck161_01028
import ReplayCheck161_01032
import ReplayCheck161_01036
import ReplayCheck161_01040
import ReplayCheck161_01044
import ReplayCheck161_01048
import ReplayCheck161_01052
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps32 (τ : Nat → Bool) (h1024 : TreeTrue τ start1024) : TreeTrue τ start1056 := by
  have h1025 : TreeTrue τ start1025 := replay_true τ ok1024 h1024
  have h1026 : TreeTrue τ start1026 := replay_true τ ok1025 h1025
  have h1027 : TreeTrue τ start1027 := replay_true τ ok1026 h1026
  have h1028 : TreeTrue τ start1028 := replay_true τ ok1027 h1027
  have h1029 : TreeTrue τ start1029 := replay_true τ ok1028 h1028
  have h1030 : TreeTrue τ start1030 := replay_true τ ok1029 h1029
  have h1031 : TreeTrue τ start1031 := replay_true τ ok1030 h1030
  have h1032 : TreeTrue τ start1032 := replay_true τ ok1031 h1031
  have h1033 : TreeTrue τ start1033 := replay_true τ ok1032 h1032
  have h1034 : TreeTrue τ start1034 := replay_true τ ok1033 h1033
  have h1035 : TreeTrue τ start1035 := replay_true τ ok1034 h1034
  have h1036 : TreeTrue τ start1036 := replay_true τ ok1035 h1035
  have h1037 : TreeTrue τ start1037 := replay_true τ ok1036 h1036
  have h1038 : TreeTrue τ start1038 := replay_true τ ok1037 h1037
  have h1039 : TreeTrue τ start1039 := replay_true τ ok1038 h1038
  have h1040 : TreeTrue τ start1040 := replay_true τ ok1039 h1039
  have h1041 : TreeTrue τ start1041 := replay_true τ ok1040 h1040
  have h1042 : TreeTrue τ start1042 := replay_true τ ok1041 h1041
  have h1043 : TreeTrue τ start1043 := replay_true τ ok1042 h1042
  have h1044 : TreeTrue τ start1044 := replay_true τ ok1043 h1043
  have h1045 : TreeTrue τ start1045 := replay_true τ ok1044 h1044
  have h1046 : TreeTrue τ start1046 := replay_true τ ok1045 h1045
  have h1047 : TreeTrue τ start1047 := replay_true τ ok1046 h1046
  have h1048 : TreeTrue τ start1048 := replay_true τ ok1047 h1047
  have h1049 : TreeTrue τ start1049 := replay_true τ ok1048 h1048
  have h1050 : TreeTrue τ start1050 := replay_true τ ok1049 h1049
  have h1051 : TreeTrue τ start1051 := replay_true τ ok1050 h1050
  have h1052 : TreeTrue τ start1052 := replay_true τ ok1051 h1051
  have h1053 : TreeTrue τ start1053 := replay_true τ ok1052 h1052
  have h1054 : TreeTrue τ start1054 := replay_true τ ok1053 h1053
  have h1055 : TreeTrue τ start1055 := replay_true τ ok1054 h1054
  have h1056 : TreeTrue τ start1056 := cp_true τ ok1055 h1055
  exact h1056
#print axioms steps32
end Snake9.ReplayFull161
