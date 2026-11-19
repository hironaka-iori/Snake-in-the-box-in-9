import LayerJoining

namespace Prefix248
open LayerJoining

def oldIndex {k m : Nat} (hk : k ≤ m) (i : Fin (k + 1)) : Fin (m + 1) :=
  ⟨i.val, by have hi := i.isLt; omega⟩

/-- Keep the first k edges of the given ordered induced path. -/
def takePrefix {V : Type} {R : V → V → Prop} {k m : Nat}
    (p : InducedPath V R m) (hk : k ≤ m) : InducedPath V R k where
  vertex i := p.vertex (oldIndex hk i)
  distinct i j h := by
    apply Fin.ext
    exact congrArg (fun t : Fin (m + 1) => t.val) (p.distinct (oldIndex hk i) (oldIndex hk j) h)
  induced i j h := p.induced (oldIndex hk i) (oldIndex hk j) h

/-- Both the prescribed root and any vertex-wise restriction survive truncation. -/
theorem rooted_prefix {V : Type} {R : V → V → Prop} {k m : Nat}
    (p : InducedPath V R m) (hk : k ≤ m) (root : V) (allowed : V → Prop)
    (hr : p.vertex ⟨0, by omega⟩ = root) (ha : ∀ i, allowed (p.vertex i)) :
    (takePrefix p hk).vertex ⟨0, by omega⟩ = root ∧ ∀ i, allowed ((takePrefix p hk).vertex i) :=
  ⟨hr, fun i => ha (oldIndex hk i)⟩

theorem compatible_prefix {V : Type} {R : V → V → Prop} {a b k : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b) (hk : k ≤ b)
    (c : Compatible p q) : Compatible p (takePrefix q hk) :=
  fun i j => c i (oldIndex hk j)

def LengthSplit (a b : Nat) : Prop :=
  (a = 96 ∧ b = 95) ∨ (a = 95 ∧ b = 96) ∨
  (a = 97 ∧ b = 94) ∨ (a = 94 ∧ b = 97) ∨
  (a = 98 ∧ b = 93) ∨ (a = 93 ∧ b = 98)

theorem exact_splits (a b : Nat) (ha : a ≤ 98) (hb : b ≤ 98) (total : a + b + 1 = 192) :
    LengthSplit a b := by
  unfold LengthSplit
  omega

/-- Keep the entire first arm, the crossing, and a prefix of the second arm. -/
theorem trim_to_192 {V : Type} {R : V → V → Prop} {a b : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b) (c : Compatible p q)
    (ha : a ≤ 98) (hb : b ≤ 98) (long : 192 ≤ a + b + 1) :
    ∃ (k : Nat) (hk : k ≤ b), a + k + 1 = 192 ∧ LengthSplit a k ∧
      Compatible p (takePrefix q hk) ∧ Nonempty (InducedPath (V × Bool) (LayerAdj R) 192) := by
  let k := 191 - a
  have hk : k ≤ b := by dsimp [k]; omega
  have total : a + k + 1 = 192 := by dsimp [k]; omega
  have compat := compatible_prefix p q hk c
  refine ⟨k, hk, total, exact_splits a k ha (Nat.le_trans hk hb) total, compat, ?_⟩
  have assembled := LayerJoining.join p (takePrefix q hk) compat
  rw [total] at assembled
  exact ⟨assembled⟩

#print axioms takePrefix
#print axioms rooted_prefix
#print axioms compatible_prefix
#print axioms exact_splits
#print axioms trim_to_192

end Prefix248
