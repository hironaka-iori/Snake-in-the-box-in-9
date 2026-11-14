import TwoStep216
import Joint216

set_option Elab.async false

namespace PathJoint216
open IndexedCriterion206 ConcreteGeometry213 ConcreteParity214

def edge (u v : Nat) : Bool := decide (hamming (word u) (word v) = 1)

/-- The actual indexed path supplies both successive edge conditions.
The outer relation must itself be necessary for that path. Native tables,
bitset interpretation and arbitrary-input normalization remain separate. -/
theorem actual_path_pair_projection
    (values : Nat → Nat) (domains : Nat → List Nat)
    (T : Nat → Nat → Bool)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ word (values (group i))))
    (g : Nat) (hg : g < 76)
    (hfit : ∀ k, values k ∈ domains k)
    (houter : T (values g) (values (g+2)) = true) :
    (edge (values g) (values (g+1)) &&
      (domains (g+2)).any (fun w => edge (values (g+1)) w && T (values g) w)) = true ∧
    (edge (values (g+1)) (values (g+2)) &&
      (domains g).any (fun u => edge u (values (g+1)) && T u (values (g+2)))) = true ∧
    (T (values g) (values (g+2)) &&
      (domains (g+1)).any (fun v => edge (values g) v && edge v (values (g+2)))) = true := by
  have h01 : edge (values g) (values (g+1)) = true := by
    simp only [edge, decide_eq_true_eq]
    exact PathParity214.free_adjacent values hp g (by omega)
  have h12 : edge (values (g+1)) (values (g+2)) = true := by
    simp only [edge, decide_eq_true_eq]
    simpa [Nat.add_assoc] using PathParity214.free_adjacent values hp (g+1) (by omega)
  exact Joint216.pair_projection_preserves
    (domains g) (domains (g+1)) (domains (g+2)) edge edge T
    (values g) (values (g+1)) (values (g+2))
    (hfit g) (hfit (g+1)) (hfit (g+2)) h01 h12 houter

#print axioms actual_path_pair_projection
end PathJoint216
