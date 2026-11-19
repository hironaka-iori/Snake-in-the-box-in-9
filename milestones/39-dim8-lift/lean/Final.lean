import Dim8Lift
import Cover2
/-! # The whole route, conditional only on finite certificates

`upper_of_certs`: for 113 ≤ L ≤ 116, if
* the cover tables `t5`, `t6` pass their checks (`decide`-checkable),
* the Q5 cover CNF and the 35 Q6 cover CNFs are unsatisfiable,
* the cube CNF of every representative in `reps` is unsatisfiable,
then every snake of Q9 has at most `2 L - 3` edges.  With L = 116 this is 229. -/
namespace Dim8Lift
open Dim8Lift.Tab Dim8Lift.Sym Dim8Lift.Cube Snake9.LocalWindow

theorem upper_of_certs {L : Nat} (h113 : 113 ≤ L) (h116 : L ≤ 116)
    (t5 : List (Nat × List Nat × Nat)) (t6 : List (Nat × Nat × List Nat × Nat)) (reps : List (Nat × Nat))
    (h5 : t5.all (fun e => chk 5 e.1 e.2.1 e.2.2) = true)
    (h6 : t6.all (fun e => chk 6 e.2.1 e.2.2.1 e.2.2.2 && reps.contains (pcN 64 e.2.2.2, e.2.2.2)) = true)
    (hU5 : Unsat (c5Cnf (t5.map (·.1))))
    (hU6 : ∀ e ∈ t5, Unsat (c6Cnf e.2.2 ((t6.filter (·.1 == e.2.2)).map (·.2.1))))
    (hcubes : ∀ r ∈ reps, Unsat (cubeCnfC4 13 L r.2 r.1)) :
    ∀ {m : Nat}, Snake9.Snake m → m ≤ 2 * L - 3 :=
  snake_le_of_noPit (by omega) h116
    (noPit_of_cubes reps h113 (by omega) (coverOK_of t5 t6 reps h5 h6 hU5 hU6) hcubes)

end Dim8Lift

#print axioms Dim8Lift.upper_of_certs
