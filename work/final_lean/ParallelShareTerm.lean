import Std

/-! Elementary semantics of the parallel-square share encoder at frozen upstream
75404cc705135dd1f0526ecc9f1d198d3fbf0366. This proves only the local Boolean gates,
not CNF applicability, a refutation, or a global snake bound. -/
namespace Snake9.ParallelShareTerm

def bit (b : Bool) : Nat := if b then 1 else 0
def others (a b c : Bool) : Nat := bit a + bit b + bit c
def gate1 (e a b c : Bool) : Bool := e && decide (others a b c ≤ 1)
def gate3 (e a b c : Bool) : Bool := e && decide (others a b c = 0)

/-- The unary leaves [E,E,g1,g3,g3,g3] have the intended weight when the
parallel square has at most three selected corners, including the centre. -/
theorem unary_weight : ∀ e a b c : Bool, others a b c ≤ 2 →
    2 * bit e + bit (gate1 e a b c) + 3 * bit (gate3 e a b c) =
      if e then 6 / (1 + others a b c) else 0 := by
  decide +kernel

/-- All clauses of the g1/g3 gates with no fixed other corner are true under
their canonical semantic assignment. The three pair clauses force g1 upward. -/
theorem unfixed_gate_clauses : ∀ e a b c : Bool,
    ((!e || a || b || gate1 e a b c) &&
     (!e || a || c || gate1 e a b c) &&
     (!e || b || c || gate1 e a b c) &&
     (!(gate1 e a b c) || !a || !b) &&
     (!(gate1 e a b c) || !a || !c) &&
     (!(gate1 e a b c) || !b || !c) &&
     (!(gate1 e a b c) || e) &&
     (!e || a || b || c || gate3 e a b c) &&
     (!(gate3 e a b c) || e) &&
     (!(gate3 e a b c) || !a) &&
     (!(gate3 e a b c) || !b) &&
     (!(gate3 e a b c) || !c)) = true := by
  decide +kernel

/-- With one fixed selected other corner, g3 vanishes and g1 means both
remaining corners are unselected. -/
theorem one_fixed_gate : ∀ e a b : Bool,
    gate3 e true a b = false ∧
    gate1 e true a b = (e && !a && !b) ∧
    ((!e || a || b || gate1 e true a b) &&
     (!(gate1 e true a b) || !a) &&
     (!(gate1 e true a b) || !b) &&
     (!(gate1 e true a b) || e)) = true := by
  decide +kernel

theorem two_fixed_gates : ∀ e a : Bool,
    gate1 e true true a = false ∧ gate3 e true true a = false := by
  decide +kernel

/-- The canonical assignment for a clipped totalizer merge satisfies a
pairwise upward implication; full circuit assembly remains a separate task. -/
theorem clipped_merge (a b s t cap : Nat) (hs : s ≤ a) (ht : t ≤ b) :
    min (s + t) cap ≤ a + b := by omega

#print axioms unary_weight
#print axioms unfixed_gate_clauses
#print axioms one_fixed_gate
#print axioms two_fixed_gates
#print axioms clipped_merge
end Snake9.ParallelShareTerm
