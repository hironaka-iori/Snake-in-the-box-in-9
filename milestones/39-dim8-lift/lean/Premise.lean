import Sums
/-! The Q8 statement the lift needs, in the form of milestone 29's CNF (without auxiliary variables).

`Pit c L D S ℓ`: `S` is a vertex set of Q8 (vertices `u < 256`; values at `u ≥ 256` are ignored) with
* no vertex of `S` having three neighbours in `S` (degree at most 2),
* a level function `ℓ ≤ D` such that every vertex (selected or not) with two neighbours in `S` has a
  neighbour in `S` of smaller level (so `S` has no cycle: look at a vertex of least level on it),
* endpoint count at most `2c`: a vertex of `S` counts once if it has at most one neighbour in `S` and once
  more if it has none (so this sum is twice the number of paths),
* at least `L` vertices.
`NoPit c L D` says no such pair exists: every induced linear forest of Q8 with at most `c` paths has fewer
than `L` vertices.  (Any induced linear forest has a level function with `D = 2^(n-2) = 64`, e.g. the
distance to the nearer end of its path; that direction is not needed here.) -/
namespace Dim8Lift

def nb (u a : Nat) : Nat := u ^^^ 2 ^ a

def anyB (S : Nat → Bool) (u : Nat) : Bool := (List.range 8).any fun a => S (nb u a)

def twoB (S : Nat → Bool) (u : Nat) : Bool :=
  (List.range 8).any fun a => (List.range 8).any fun a' => decide (a < a') && S (nb u a) && S (nb u a')

def endW (S : Nat → Bool) (u : Nat) : Nat :=
  (if S u && !twoB S u then 1 else 0) + (if S u && !anyB S u then 1 else 0)

structure Pit (c L D : Nat) (S : Nat → Bool) (ℓ : Nat → Nat) : Prop where
  deg : ∀ u, u < 256 → ∀ a a' a'', a < a' → a' < a'' → a'' < 8 →
    S u = true → S (nb u a) = true → S (nb u a') = true → S (nb u a'') = false
  lvl_le : ∀ u, u < 256 → ℓ u ≤ D
  lvl : ∀ u, u < 256 → twoB S u = true → ∃ a, a < 8 ∧ S (nb u a) = true ∧ ℓ (nb u a) < ℓ u
  ends : sm 256 (endW S) ≤ 2 * c
  card : L ≤ cnt 256 S

def NoPit (c L D : Nat) : Prop := ∀ (S : Nat → Bool) (ℓ : Nat → Nat), ¬ Pit c L D S ℓ

end Dim8Lift
