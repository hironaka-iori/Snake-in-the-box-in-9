import ReplayCheck161_00096
import ReplayCheck161_00100
import ReplayCheck161_00104
import ReplayCheck161_00108
import ReplayCheck161_00112
import ReplayCheck161_00116
import ReplayCheck161_00120
import ReplayCheck161_00124
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps3 (τ : Nat → Bool) (h96 : TreeTrue τ start96) : TreeTrue τ start128 := by
  have h97 : TreeTrue τ start97 := replay_true τ ok96 h96
  have h98 : TreeTrue τ start98 := replay_true τ ok97 h97
  have h99 : TreeTrue τ start99 := replay_true τ ok98 h98
  have h100 : TreeTrue τ start100 := replay_true τ ok99 h99
  have h101 : TreeTrue τ start101 := replay_true τ ok100 h100
  have h102 : TreeTrue τ start102 := replay_true τ ok101 h101
  have h103 : TreeTrue τ start103 := replay_true τ ok102 h102
  have h104 : TreeTrue τ start104 := replay_true τ ok103 h103
  have h105 : TreeTrue τ start105 := replay_true τ ok104 h104
  have h106 : TreeTrue τ start106 := replay_true τ ok105 h105
  have h107 : TreeTrue τ start107 := replay_true τ ok106 h106
  have h108 : TreeTrue τ start108 := replay_true τ ok107 h107
  have h109 : TreeTrue τ start109 := replay_true τ ok108 h108
  have h110 : TreeTrue τ start110 := replay_true τ ok109 h109
  have h111 : TreeTrue τ start111 := replay_true τ ok110 h110
  have h112 : TreeTrue τ start112 := replay_true τ ok111 h111
  have h113 : TreeTrue τ start113 := replay_true τ ok112 h112
  have h114 : TreeTrue τ start114 := replay_true τ ok113 h113
  have h115 : TreeTrue τ start115 := replay_true τ ok114 h114
  have h116 : TreeTrue τ start116 := replay_true τ ok115 h115
  have h117 : TreeTrue τ start117 := replay_true τ ok116 h116
  have h118 : TreeTrue τ start118 := replay_true τ ok117 h117
  have h119 : TreeTrue τ start119 := replay_true τ ok118 h118
  have h120 : TreeTrue τ start120 := replay_true τ ok119 h119
  have h121 : TreeTrue τ start121 := replay_true τ ok120 h120
  have h122 : TreeTrue τ start122 := replay_true τ ok121 h121
  have h123 : TreeTrue τ start123 := replay_true τ ok122 h122
  have h124 : TreeTrue τ start124 := replay_true τ ok123 h123
  have h125 : TreeTrue τ start125 := replay_true τ ok124 h124
  have h126 : TreeTrue τ start126 := replay_true τ ok125 h125
  have h127 : TreeTrue τ start127 := replay_true τ ok126 h126
  have h128 : TreeTrue τ start128 := cp_true τ ok127 h127
  exact h128
#print axioms steps3
end Snake9.ReplayFull161
