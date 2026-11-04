import ReplayCheck161_01056
import ReplayCheck161_01060
import ReplayCheck161_01064
import ReplayCheck161_01068
import ReplayCheck161_01072
import ReplayCheck161_01076
import ReplayCheck161_01080
import ReplayCheck161_01084
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps33 (τ : Nat → Bool) (h1056 : TreeTrue τ start1056) : TreeTrue τ start1088 := by
  have h1057 : TreeTrue τ start1057 := replay_true τ ok1056 h1056
  have h1058 : TreeTrue τ start1058 := replay_true τ ok1057 h1057
  have h1059 : TreeTrue τ start1059 := replay_true τ ok1058 h1058
  have h1060 : TreeTrue τ start1060 := replay_true τ ok1059 h1059
  have h1061 : TreeTrue τ start1061 := replay_true τ ok1060 h1060
  have h1062 : TreeTrue τ start1062 := replay_true τ ok1061 h1061
  have h1063 : TreeTrue τ start1063 := replay_true τ ok1062 h1062
  have h1064 : TreeTrue τ start1064 := replay_true τ ok1063 h1063
  have h1065 : TreeTrue τ start1065 := replay_true τ ok1064 h1064
  have h1066 : TreeTrue τ start1066 := replay_true τ ok1065 h1065
  have h1067 : TreeTrue τ start1067 := replay_true τ ok1066 h1066
  have h1068 : TreeTrue τ start1068 := replay_true τ ok1067 h1067
  have h1069 : TreeTrue τ start1069 := replay_true τ ok1068 h1068
  have h1070 : TreeTrue τ start1070 := replay_true τ ok1069 h1069
  have h1071 : TreeTrue τ start1071 := replay_true τ ok1070 h1070
  have h1072 : TreeTrue τ start1072 := replay_true τ ok1071 h1071
  have h1073 : TreeTrue τ start1073 := replay_true τ ok1072 h1072
  have h1074 : TreeTrue τ start1074 := replay_true τ ok1073 h1073
  have h1075 : TreeTrue τ start1075 := replay_true τ ok1074 h1074
  have h1076 : TreeTrue τ start1076 := replay_true τ ok1075 h1075
  have h1077 : TreeTrue τ start1077 := replay_true τ ok1076 h1076
  have h1078 : TreeTrue τ start1078 := replay_true τ ok1077 h1077
  have h1079 : TreeTrue τ start1079 := replay_true τ ok1078 h1078
  have h1080 : TreeTrue τ start1080 := replay_true τ ok1079 h1079
  have h1081 : TreeTrue τ start1081 := replay_true τ ok1080 h1080
  have h1082 : TreeTrue τ start1082 := replay_true τ ok1081 h1081
  have h1083 : TreeTrue τ start1083 := replay_true τ ok1082 h1082
  have h1084 : TreeTrue τ start1084 := replay_true τ ok1083 h1083
  have h1085 : TreeTrue τ start1085 := replay_true τ ok1084 h1084
  have h1086 : TreeTrue τ start1086 := replay_true τ ok1085 h1085
  have h1087 : TreeTrue τ start1087 := replay_true τ ok1086 h1086
  have h1088 : TreeTrue τ start1088 := cp_true τ ok1087 h1087
  exact h1088
#print axioms steps33
end Snake9.ReplayFull161
