import ReplayCheck161_00064
import ReplayCheck161_00068
import ReplayCheck161_00072
import ReplayCheck161_00076
import ReplayCheck161_00080
import ReplayCheck161_00084
import ReplayCheck161_00088
import ReplayCheck161_00092
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps2 (τ : Nat → Bool) (h64 : TreeTrue τ start64) : TreeTrue τ start96 := by
  have h65 : TreeTrue τ start65 := replay_true τ ok64 h64
  have h66 : TreeTrue τ start66 := replay_true τ ok65 h65
  have h67 : TreeTrue τ start67 := replay_true τ ok66 h66
  have h68 : TreeTrue τ start68 := replay_true τ ok67 h67
  have h69 : TreeTrue τ start69 := replay_true τ ok68 h68
  have h70 : TreeTrue τ start70 := replay_true τ ok69 h69
  have h71 : TreeTrue τ start71 := replay_true τ ok70 h70
  have h72 : TreeTrue τ start72 := replay_true τ ok71 h71
  have h73 : TreeTrue τ start73 := replay_true τ ok72 h72
  have h74 : TreeTrue τ start74 := replay_true τ ok73 h73
  have h75 : TreeTrue τ start75 := replay_true τ ok74 h74
  have h76 : TreeTrue τ start76 := replay_true τ ok75 h75
  have h77 : TreeTrue τ start77 := replay_true τ ok76 h76
  have h78 : TreeTrue τ start78 := replay_true τ ok77 h77
  have h79 : TreeTrue τ start79 := replay_true τ ok78 h78
  have h80 : TreeTrue τ start80 := replay_true τ ok79 h79
  have h81 : TreeTrue τ start81 := replay_true τ ok80 h80
  have h82 : TreeTrue τ start82 := replay_true τ ok81 h81
  have h83 : TreeTrue τ start83 := replay_true τ ok82 h82
  have h84 : TreeTrue τ start84 := replay_true τ ok83 h83
  have h85 : TreeTrue τ start85 := replay_true τ ok84 h84
  have h86 : TreeTrue τ start86 := replay_true τ ok85 h85
  have h87 : TreeTrue τ start87 := replay_true τ ok86 h86
  have h88 : TreeTrue τ start88 := replay_true τ ok87 h87
  have h89 : TreeTrue τ start89 := replay_true τ ok88 h88
  have h90 : TreeTrue τ start90 := replay_true τ ok89 h89
  have h91 : TreeTrue τ start91 := replay_true τ ok90 h90
  have h92 : TreeTrue τ start92 := replay_true τ ok91 h91
  have h93 : TreeTrue τ start93 := replay_true τ ok92 h92
  have h94 : TreeTrue τ start94 := replay_true τ ok93 h93
  have h95 : TreeTrue τ start95 := replay_true τ ok94 h94
  have h96 : TreeTrue τ start96 := cp_true τ ok95 h95
  exact h96
#print axioms steps2
end Snake9.ReplayFull161
