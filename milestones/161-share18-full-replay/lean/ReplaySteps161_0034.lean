import ReplayCheck161_01088
import ReplayCheck161_01092
import ReplayCheck161_01096
import ReplayCheck161_01100
import ReplayCheck161_01104
import ReplayCheck161_01108
import ReplayCheck161_01112
import ReplayCheck161_01116
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps34 (τ : Nat → Bool) (h1088 : TreeTrue τ start1088) : TreeTrue τ start1120 := by
  have h1089 : TreeTrue τ start1089 := replay_true τ ok1088 h1088
  have h1090 : TreeTrue τ start1090 := replay_true τ ok1089 h1089
  have h1091 : TreeTrue τ start1091 := replay_true τ ok1090 h1090
  have h1092 : TreeTrue τ start1092 := replay_true τ ok1091 h1091
  have h1093 : TreeTrue τ start1093 := replay_true τ ok1092 h1092
  have h1094 : TreeTrue τ start1094 := replay_true τ ok1093 h1093
  have h1095 : TreeTrue τ start1095 := replay_true τ ok1094 h1094
  have h1096 : TreeTrue τ start1096 := replay_true τ ok1095 h1095
  have h1097 : TreeTrue τ start1097 := replay_true τ ok1096 h1096
  have h1098 : TreeTrue τ start1098 := replay_true τ ok1097 h1097
  have h1099 : TreeTrue τ start1099 := replay_true τ ok1098 h1098
  have h1100 : TreeTrue τ start1100 := replay_true τ ok1099 h1099
  have h1101 : TreeTrue τ start1101 := replay_true τ ok1100 h1100
  have h1102 : TreeTrue τ start1102 := replay_true τ ok1101 h1101
  have h1103 : TreeTrue τ start1103 := replay_true τ ok1102 h1102
  have h1104 : TreeTrue τ start1104 := replay_true τ ok1103 h1103
  have h1105 : TreeTrue τ start1105 := replay_true τ ok1104 h1104
  have h1106 : TreeTrue τ start1106 := replay_true τ ok1105 h1105
  have h1107 : TreeTrue τ start1107 := replay_true τ ok1106 h1106
  have h1108 : TreeTrue τ start1108 := replay_true τ ok1107 h1107
  have h1109 : TreeTrue τ start1109 := replay_true τ ok1108 h1108
  have h1110 : TreeTrue τ start1110 := replay_true τ ok1109 h1109
  have h1111 : TreeTrue τ start1111 := replay_true τ ok1110 h1110
  have h1112 : TreeTrue τ start1112 := replay_true τ ok1111 h1111
  have h1113 : TreeTrue τ start1113 := replay_true τ ok1112 h1112
  have h1114 : TreeTrue τ start1114 := replay_true τ ok1113 h1113
  have h1115 : TreeTrue τ start1115 := replay_true τ ok1114 h1114
  have h1116 : TreeTrue τ start1116 := replay_true τ ok1115 h1115
  have h1117 : TreeTrue τ start1117 := replay_true τ ok1116 h1116
  have h1118 : TreeTrue τ start1118 := replay_true τ ok1117 h1117
  have h1119 : TreeTrue τ start1119 := replay_true τ ok1118 h1118
  have h1120 : TreeTrue τ start1120 := cp_true τ ok1119 h1119
  exact h1120
#print axioms steps34
end Snake9.ReplayFull161
