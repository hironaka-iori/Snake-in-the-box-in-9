import ReplayCheck161_01120
import ReplayCheck161_01124
import ReplayCheck161_01128
import ReplayCheck161_01132
import ReplayCheck161_01136
import ReplayCheck161_01140
import ReplayCheck161_01144
import ReplayCheck161_01148
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps35 (τ : Nat → Bool) (h1120 : TreeTrue τ start1120) : TreeTrue τ start1152 := by
  have h1121 : TreeTrue τ start1121 := replay_true τ ok1120 h1120
  have h1122 : TreeTrue τ start1122 := replay_true τ ok1121 h1121
  have h1123 : TreeTrue τ start1123 := replay_true τ ok1122 h1122
  have h1124 : TreeTrue τ start1124 := replay_true τ ok1123 h1123
  have h1125 : TreeTrue τ start1125 := replay_true τ ok1124 h1124
  have h1126 : TreeTrue τ start1126 := replay_true τ ok1125 h1125
  have h1127 : TreeTrue τ start1127 := replay_true τ ok1126 h1126
  have h1128 : TreeTrue τ start1128 := replay_true τ ok1127 h1127
  have h1129 : TreeTrue τ start1129 := replay_true τ ok1128 h1128
  have h1130 : TreeTrue τ start1130 := replay_true τ ok1129 h1129
  have h1131 : TreeTrue τ start1131 := replay_true τ ok1130 h1130
  have h1132 : TreeTrue τ start1132 := replay_true τ ok1131 h1131
  have h1133 : TreeTrue τ start1133 := replay_true τ ok1132 h1132
  have h1134 : TreeTrue τ start1134 := replay_true τ ok1133 h1133
  have h1135 : TreeTrue τ start1135 := replay_true τ ok1134 h1134
  have h1136 : TreeTrue τ start1136 := replay_true τ ok1135 h1135
  have h1137 : TreeTrue τ start1137 := replay_true τ ok1136 h1136
  have h1138 : TreeTrue τ start1138 := replay_true τ ok1137 h1137
  have h1139 : TreeTrue τ start1139 := replay_true τ ok1138 h1138
  have h1140 : TreeTrue τ start1140 := replay_true τ ok1139 h1139
  have h1141 : TreeTrue τ start1141 := replay_true τ ok1140 h1140
  have h1142 : TreeTrue τ start1142 := replay_true τ ok1141 h1141
  have h1143 : TreeTrue τ start1143 := replay_true τ ok1142 h1142
  have h1144 : TreeTrue τ start1144 := replay_true τ ok1143 h1143
  have h1145 : TreeTrue τ start1145 := replay_true τ ok1144 h1144
  have h1146 : TreeTrue τ start1146 := replay_true τ ok1145 h1145
  have h1147 : TreeTrue τ start1147 := replay_true τ ok1146 h1146
  have h1148 : TreeTrue τ start1148 := replay_true τ ok1147 h1147
  have h1149 : TreeTrue τ start1149 := replay_true τ ok1148 h1148
  have h1150 : TreeTrue τ start1150 := replay_true τ ok1149 h1149
  have h1151 : TreeTrue τ start1151 := replay_true τ ok1150 h1150
  have h1152 : TreeTrue τ start1152 := cp_true τ ok1151 h1151
  exact h1152
#print axioms steps35
end Snake9.ReplayFull161
