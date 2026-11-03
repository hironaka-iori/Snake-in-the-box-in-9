import Recovered122G.LocalWindowSat.End26
import Recovered122G.LocalWindowUnsat.End26

namespace Snake9.LocalEndpoint26122
open Snake9.LocalWindow

theorem endpoints_in_common (S E : Nat → Bool)
    (ax : Axioms S E (winOf [0,1,2,0,3,2])
      (centresOf (winOf [0,1,2,0,3,2]) [(0,21),(0,2),(0,21),(0,6),(0,21)]))
    (v : Nat) (hE : E v = true) :
    v ∈ ([0,5,10,15,18,23,34,39,66,71,130,135,258,263] : List Nat) := by
  apply Classical.byContradiction
  intro hc
  have hv := ax.sel_lt v (ax.end_sel v hE)
  obtain ⟨τ, hτ⟩ := End26.sat S E ax ⟨v, hv, hE, hc⟩
  rw [End26.unsat τ] at hτ
  exact Bool.false_ne_true hτ

end Snake9.LocalEndpoint26122
#print axioms Snake9.LocalEndpoint26122.endpoints_in_common
