import ReplayCheck161_00128
import ReplayCheck161_00132
import ReplayCheck161_00136
import ReplayCheck161_00140
import ReplayCheck161_00144
import ReplayCheck161_00148
import ReplayCheck161_00152
import ReplayCheck161_00156
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps4 (τ : Nat → Bool) (h128 : TreeTrue τ start128) : TreeTrue τ start160 := by
  have h129 : TreeTrue τ start129 := replay_true τ ok128 h128
  have h130 : TreeTrue τ start130 := replay_true τ ok129 h129
  have h131 : TreeTrue τ start131 := replay_true τ ok130 h130
  have h132 : TreeTrue τ start132 := replay_true τ ok131 h131
  have h133 : TreeTrue τ start133 := replay_true τ ok132 h132
  have h134 : TreeTrue τ start134 := replay_true τ ok133 h133
  have h135 : TreeTrue τ start135 := replay_true τ ok134 h134
  have h136 : TreeTrue τ start136 := replay_true τ ok135 h135
  have h137 : TreeTrue τ start137 := replay_true τ ok136 h136
  have h138 : TreeTrue τ start138 := replay_true τ ok137 h137
  have h139 : TreeTrue τ start139 := replay_true τ ok138 h138
  have h140 : TreeTrue τ start140 := replay_true τ ok139 h139
  have h141 : TreeTrue τ start141 := replay_true τ ok140 h140
  have h142 : TreeTrue τ start142 := replay_true τ ok141 h141
  have h143 : TreeTrue τ start143 := replay_true τ ok142 h142
  have h144 : TreeTrue τ start144 := replay_true τ ok143 h143
  have h145 : TreeTrue τ start145 := replay_true τ ok144 h144
  have h146 : TreeTrue τ start146 := replay_true τ ok145 h145
  have h147 : TreeTrue τ start147 := replay_true τ ok146 h146
  have h148 : TreeTrue τ start148 := replay_true τ ok147 h147
  have h149 : TreeTrue τ start149 := replay_true τ ok148 h148
  have h150 : TreeTrue τ start150 := replay_true τ ok149 h149
  have h151 : TreeTrue τ start151 := replay_true τ ok150 h150
  have h152 : TreeTrue τ start152 := replay_true τ ok151 h151
  have h153 : TreeTrue τ start153 := replay_true τ ok152 h152
  have h154 : TreeTrue τ start154 := replay_true τ ok153 h153
  have h155 : TreeTrue τ start155 := replay_true τ ok154 h154
  have h156 : TreeTrue τ start156 := replay_true τ ok155 h155
  have h157 : TreeTrue τ start157 := replay_true τ ok156 h156
  have h158 : TreeTrue τ start158 := replay_true τ ok157 h157
  have h159 : TreeTrue τ start159 := replay_true τ ok158 h158
  have h160 : TreeTrue τ start160 := cp_true τ ok159 h159
  exact h160
#print axioms steps4
end Snake9.ReplayFull161
