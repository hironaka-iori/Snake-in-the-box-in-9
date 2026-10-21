import ParallelShareBoolean

/-! The values assigned to concrete totalizer variables are thresholds of sums
of actual geometric terms. Sublist membership preserves multiplicity and makes
every block bounded by the complete window share. -/
namespace Snake9.ParallelShareBlocks
open Snake9.LocalWindow Snake9.ParallelShareTerm Snake9.ParallelShareBoolean

structure Term where
  v : Nat
  k : Nat
  a : Nat
  b : Nat
deriving Repr, DecidableEq

def Term.value (S : Nat → Bool) (t : Term) : Nat :=
  parallelTerm S t.v t.k (t.a, t.b)

def atCentre (v : Nat) : List Term :=
  (List.range 9).flatMap fun k => (freePairs 9 9).map fun ab => ⟨v, k, ab.1, ab.2⟩

def allTerms (cs : List Centre) : List Term := cs.flatMap fun c => atCentre c.v
def mass (S : Nat → Bool) (ts : List Term) : Nat := (ts.map (Term.value S)).sum
def block (ts : List Term) (lo hi : Nat) : List Term := (ts.drop lo).take (hi - lo)
def blockMass (S : Nat → Bool) (ts : List Term) (lo hi : Nat) : Nat := mass S (block ts lo hi)

theorem sum_append_nat (xs ys : List Nat) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

theorem sum_flat {α β : Type} (xs : List α) (f : α → List β) (g : β → Nat) :
    ((xs.flatMap f).map g).sum = (xs.map fun a => ((f a).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.map_append, sum_append_nat,
      List.map_cons, List.sum_cons, ih]

theorem mass_atCentre (S : Nat → Bool) (v : Nat) : mass S (atCentre v) = parallelShare S v := by
  simp only [mass, atCentre, sum_flat, List.map_map, Term.value, parallelShare]
  rfl

theorem mass_allTerms (S : Nat → Bool) (cs : List Centre) :
    mass S (allTerms cs) = parallelSum S cs := by
  unfold mass allTerms parallelSum
  rw [sum_flat]
  exact congrArg List.sum (List.map_congr_left (fun c _ => mass_atCentre S c.v))

theorem sum_sublist_le : ∀ {xs ys : List Nat}, xs.Sublist ys → xs.sum ≤ ys.sum
  | _, _, .slnil => by simp
  | _, _, .cons a h => by rw [List.sum_cons]; have := sum_sublist_le h; omega
  | _, _, .cons₂ a h => by rw [List.sum_cons, List.sum_cons]; have := sum_sublist_le h; omega

theorem mass_sublist_le (S : Nat → Bool) {xs ys : List Term} (h : xs.Sublist ys) :
    mass S xs ≤ mass S ys := sum_sublist_le (h.map (Term.value S))

theorem mass_append (S : Nat → Bool) (xs ys : List Term) :
    mass S (xs ++ ys) = mass S xs + mass S ys := by simp [mass, sum_append_nat]

theorem block_split (ts : List Term) {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    block ts lo hi = block ts lo mid ++ block ts mid hi := by
  unfold block
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, List.take_add, List.drop_drop,
    show lo + (mid - lo) = mid by omega]

theorem blockMass_split (S : Nat → Bool) (ts : List Term) {lo mid hi : Nat}
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    blockMass S ts lo hi = blockMass S ts lo mid + blockMass S ts mid hi := by
  unfold blockMass
  rw [block_split ts h1 h2, mass_append]

theorem blockMass_total (S : Nat → Bool) (ts : List Term) (lo hi : Nat) :
    blockMass S ts lo hi ≤ mass S ts :=
  mass_sublist_le S ((List.take_sublist _ _).trans (List.drop_sublist _ _))

theorem blockMass_sub (S : Nat → Bool) (ts : List Term) {lo l h hi : Nat}
    (h1 : lo ≤ l) (h2 : l ≤ h) (h3 : h ≤ hi) :
    blockMass S ts l h ≤ blockMass S ts lo hi := by
  have a := blockMass_split S ts h1 (show l ≤ hi by omega)
  have b := blockMass_split S ts h2 h3
  omega

theorem blockMass_pair (S : Nat → Bool) (ts : List Term) {lo l1 h1 l2 h2 hi : Nat}
    (h : lo ≤ l1 ∧ l1 ≤ h1 ∧ h1 ≤ l2 ∧ l2 ≤ h2 ∧ h2 ≤ hi) :
    blockMass S ts l1 h1 + blockMass S ts l2 h2 ≤ blockMass S ts lo hi := by
  have a := blockMass_split S ts h.1 (show l1 ≤ hi by omega)
  have b := blockMass_split S ts h.2.1 (show h1 ≤ hi by omega)
  have c := blockMass_split S ts h.2.2.1 (show l2 ≤ hi by omega)
  have d := blockMass_split S ts h.2.2.2.1 h.2.2.2.2
  omega

theorem blockMass_cap {S E : Nat → Bool} {w : List Nat} {cs : List Centre} {cap : Nat}
    (ax : AxiomsP S E w cs cap) {ts : List Term} (ht : ts.Sublist (allTerms cs))
    (lo hi : Nat) : blockMass S ts lo hi ≤ cap := by
  have h := mass_sublist_le S ht
  rw [mass_allTerms] at h
  exact Nat.le_trans (blockMass_total S ts lo hi) (Nat.le_trans h ax.share_le)

def Term.valid (w : List Nat) (t : Term) : Prop :=
  t.v ∈ w ∧ t.a < t.b ∧ t.b < 9 ∧ t.k < 9 ∧ t.k ≠ t.a ∧ t.k ≠ t.b

instance (w : List Nat) (t : Term) : Decidable (t.valid w) := by
  unfold Term.valid; infer_instance

def Term.leaf (t : Term) (s : Nat) : Formula :=
  let e := square (t.v ^^^ 2 ^ t.k) t.a t.b
  let x := t.v ^^^ 2 ^ t.a
  let y := t.v ^^^ 2 ^ t.b
  let z := t.v ^^^ 2 ^ t.a ^^^ 2 ^ t.b
  if s ≤ 2 then e else if s = 3 then one e x y z else zero e x y z

def unaryBit (e x y z : Bool) (s : Nat) : Bool :=
  if s ≤ 2 then e else if s = 3 then gate1 e x y z else gate3 e x y z

theorem unaryBit_sem (e x y z : Bool) {s : Nat} (hs : 1 ≤ s) (hs' : s ≤ 6) :
    unaryBit e x y z s = decide (s ≤ 2 * bit e + bit (gate1 e x y z) + 3 * bit (gate3 e x y z)) := by
  have h : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases e <;> cases x <;> cases y <;> cases z <;> rfl

theorem Term.leaf_sem {S E : Nat → Bool} {w : List Nat} {cs : List Centre}
    (ax : Axioms S E w cs) (t : Term) (ht : t.valid w) {s : Nat}
    (hs : 1 ≤ s) (hs' : s ≤ 6) :
    (t.leaf s).eval S = decide (s ≤ t.value S) := by
  have hv := ax.window_sel t.v ht.1
  have hw := ax.parallel_unary_weight t.v t.k t.a t.b (by have := ht.2.1; have := ht.2.2.1; omega)
    ht.2.2.1 (by have := ht.2.1; omega) hv ht.2.2.2.2.1 ht.2.2.2.2.2
  unfold Term.value
  rw [hw]
  have hf : (t.leaf s).eval S = unaryBit (emptyPred S (t.v ^^^ 2 ^ t.k) (t.a, t.b))
      (S (t.v ^^^ 2 ^ t.a)) (S (t.v ^^^ 2 ^ t.b)) (S (t.v ^^^ 2 ^ t.a ^^^ 2 ^ t.b)) s := by
    unfold Term.leaf unaryBit
    split
    · exact square_eval S _ _ _
    · split
      · rw [one_eval, square_eval]
      · rw [zero_eval, square_eval]
  rw [hf]
  exact unaryBit_sem _ _ _ _ hs hs'

#print axioms blockMass_cap
#print axioms blockMass_pair
#print axioms Term.leaf_sem
end Snake9.ParallelShareBlocks
