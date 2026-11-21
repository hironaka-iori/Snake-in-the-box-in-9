import Std

namespace SegmentClosure253

variable {V : Type}

/-- These shapes can serve as sources of another regrowth step. Both the
initial and the subsequently reached shapes meet the relay length threshold. -/
inductive Relay (seed : V → Prop) (edges : V → Nat) (minEdges : Nat)
    (move : V → V → Prop) : V → Prop where
  | start {v} : seed v → minEdges ≤ edges v → Relay seed edges minEdges move v
  | step {a b} : Relay seed edges minEdges move a → move a b → minEdges ≤ edges b →
      Relay seed edges minEdges move b

/-- A terminal move needs a reachable source. Its target may be shorter. -/
def Terminal (seed : V → Prop) (edges : V → Nat) (minEdges : Nat)
    (move : V → V → Prop) (v : V) : Prop :=
  ∃ a, Relay seed edges minEdges move a ∧ move a v

variable {seed : V → Prop} {edges : V → Nat} {minEdges : Nat} {move : V → V → Prop}

/-- An outgoing cover certifies completeness; a strictly decreasing
predecessor rank certifies that every entry is actually reachable.
The hypotheses concern the move relation on shapes, including all
allowed representatives and orientations in its concrete definition. -/
theorem relay_iff_listed (listed : List V) (rank : V → Nat)
    (starts : ∀ a, seed a → minEdges ≤ edges a → a ∈ listed)
    (longEnough : ∀ a, a ∈ listed → minEdges ≤ edges a)
    (closed : ∀ a b, a ∈ listed → move a b → minEdges ≤ edges b → b ∈ listed)
    (predecessor : ∀ a, a ∈ listed → seed a ∨
      ∃ p, p ∈ listed ∧ rank p < rank a ∧ move p a)
    (v : V) : Relay seed edges minEdges move v ↔ v ∈ listed := by
  constructor
  · intro reached
    induction reached with
    | start hs hl => exact starts _ hs hl
    | step _ hm hl ih => exact closed _ _ ih hm hl
  · intro member
    have byRank : ∀ n a, rank a ≤ n → a ∈ listed → Relay seed edges minEdges move a := by
      intro n
      induction n with
      | zero =>
        intro a h ha
        rcases predecessor a ha with hs | ⟨p, _, hp, _⟩
        · exact .start hs (longEnough a ha)
        · omega
      | succ n ih =>
        intro a h ha
        rcases predecessor a ha with hs | ⟨p, hp, lower, hm⟩
        · exact .start hs (longEnough a ha)
        · exact .step (ih p (by omega) hp) hm (longEnough a ha)
    exact byRank (rank v) v (Nat.le_refl _) member

/-- The terminal list is exact when all moves out of the relay list are
covered and every terminal entry supplies a source and an actual move. -/
theorem terminal_iff_listed (relays terminals : List V)
    (relayExact : ∀ v, Relay seed edges minEdges move v ↔ v ∈ relays)
    (outgoing : ∀ a b, a ∈ relays → move a b → b ∈ terminals)
    (incoming : ∀ b, b ∈ terminals → ∃ a, a ∈ relays ∧ move a b)
    (v : V) : Terminal seed edges minEdges move v ↔ v ∈ terminals := by
  constructor
  · rintro ⟨a, ha, hm⟩
    exact outgoing a v ((relayExact a).mp ha) hm
  · intro hv
    obtain ⟨a, ha, hm⟩ := incoming v hv
    exact ⟨a, (relayExact a).mpr ha, hm⟩

/-- Transfer a certified partner bound for every listed terminal to
every admissible single-crossing join. Here 'fits v k' can quantify
over either endpoint and every compatible partner of k edges. -/
theorem joined_bound (terminals : List V) (fits : V → Nat → Prop) (cap : Nat)
    (terminalCover : ∀ v, Terminal seed edges minEdges move v → v ∈ terminals)
    (caps : ∀ v, v ∈ terminals → ∀ k, fits v k → edges v + 1 + k ≤ cap)
    {v : V} {k : Nat} (ht : Terminal seed edges minEdges move v) (hf : fits v k) :
    edges v + 1 + k ≤ cap :=
  caps v (terminalCover v ht) k hf

#print axioms relay_iff_listed
#print axioms terminal_iff_listed
#print axioms joined_bound

end SegmentClosure253
