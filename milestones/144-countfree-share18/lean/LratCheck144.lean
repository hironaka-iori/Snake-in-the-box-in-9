import LocalWindowModel

/-!
# A kernel-evaluable LRAT checker

Literals are bits of a `Nat`: variable `v < OFF` is bit `v`, its negation bit `v + OFF`,
where `OFF = 8192`.  In general bit `b` means `τ (b % OFF)` flipped `b / OFF` times
(`bitTrue`), so the negation of bit `b` is bit `b + OFF` or `b - OFF`.  A clause is the
`Nat` of its literals.

The clause database is a binary search tree keyed by slot numbers.  Proof data are
lists of `Nat`s, one per lemma, holding 13-bit words (lowest first):

  `slot  (lit+1) … (lit+1)  0  hint … hint  0`

(a hint is the slot of a database clause).  `check` runs reverse unit propagation for
each lemma; `replay` inserts the lemmas without checking anything.  Soundness:
`check t ps = true` and all clauses of `t` true imply all clauses of `replay t ps` true.

Every function evaluated by the kernel is written with recursors so that kernel
reduction does few unfoldings, and forces the database at each step so that no long
chains of suspended terms build up.
-/

namespace Snake9.Lrat144

open Snake9.LocalWindow

noncomputable section

/-- Kernel branch `if c then t else e`, written with `Bool.rec`. -/
local macro "kif " c:term " then " t:term " else " e:term : term =>
  `(Bool.rec (motive := fun _ => _) $e $t $c)

/-- Binary search tree `node key clause left right`. -/
inductive Tree where
  | nil : Tree
  | node (k c : Nat) (l r : Tree) : Tree

/-- Continue with the clause stored under key `k` (or with `dflt`). -/
def lookB (t : Tree) (k : Nat) (dflt : Bool) (f : Nat → Bool) : Bool :=
  Tree.rec (motive := fun _ => Bool) dflt
    (fun key c _ _ fl fr => kif k.blt key then fl else kif k.beq key then f c else fr) t

def lookT (t : Tree) (k : Nat) (dflt : Tree) (f : Nat → Tree) : Tree :=
  Tree.rec (motive := fun _ => Tree) dflt
    (fun key c _ _ fl fr => kif k.blt key then fl else kif k.beq key then f c else fr) t

/-- Evaluate `t` before continuing with `r`. -/
def seqT (t r : Tree) : Tree := Tree.rec (motive := fun _ => Tree) r (fun _ _ _ _ _ _ => r) t

/-- Store clause `c` under key `k`. -/
def setT (t : Tree) (k c : Nat) : Tree :=
  Tree.rec (motive := fun _ => Tree) (Tree.node k c .nil .nil)
    (fun key c' l r fl fr =>
      kif k.blt key then Tree.node key c' fl r else
      kif k.beq key then Tree.node key c l r else Tree.node key c' l fr) t

/-- `setT`, then evaluate the path to `k`. -/
def insertF (t : Tree) (k c : Nat) : Tree :=
  let t' := setT t k c
  lookT t' k t' (fun _ => t')

/-- Copies of `setT`/`insertF` used by `replay`, so that the trees of `replay` and of
`check` are different terms (the kernel caches compare equal-looking terms deeply). -/
def setT' (t : Tree) (k c : Nat) : Tree :=
  Tree.rec (motive := fun _ => Tree) (Tree.node k c .nil .nil)
    (fun key c' l r fl fr =>
      kif k.blt key then Tree.node key c' fl r else
      kif k.beq key then Tree.node key c l r else Tree.node key c' l fr) t

def insertF' (t : Tree) (k c : Nat) : Tree :=
  let t' := setT' t k c
  lookT t' k t' (fun _ => t')

/-! ## Lemmas -/

/-- Read the literal words of a lemma: returns the clause and the remaining words. -/
def litsL (fuel : Nat) : Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun c x => (c, x))
    (fun _ ih c x =>
      kif (x &&& 8191).beq 0 then (c, x >>> 13)
      else ih (c ||| (1 <<< ((x &&& 8191) - 1))) (x >>> 13)) fuel

def lemC (x : Nat) : Nat := (litsL 255 0 (x >>> 13)).1
def lemH (x : Nat) : Nat := (litsL 255 0 (x >>> 13)).2

/-- After looking up a hint clause: `u` are its literals not known to be false. -/
def hstep (ih : Nat → Nat → Bool) (z x u : Nat) : Bool :=
  kif u.beq 0 then true else
  kif (u &&& (u - 1)).beq 0 then
    ih (kif u.blt (2 ^ 8192) then z ||| (u <<< 8192) else z ||| (u >>> 8192)) x
  else ih z x

/-- Unit propagation over the hint words `x`; `z` holds the literals known false.
Returns `true` iff a conflict is reached.  The terminating word `0` is not a key, so
the lookup falls back to `false`. -/
def hints (db : Tree) (fuel : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih z x =>
      lookB db (x &&& 8191) false (fun d => hstep ih z (x >>> 13) (d ^^^ (d &&& z)))) fuel

def rup (t : Tree) (x : Nat) : Bool := hints t 4095 (lemC x) (lemH x)

def ins (t : Tree) (x : Nat) : Tree := insertF t (x &&& 8191) (lemC x)
def ins' (t : Tree) (x : Nat) : Tree := insertF' t (x &&& 8191) (lemC x)

def andB (a b : Bool) : Bool := kif a then b else false

def check (t : Tree) (ps : List Nat) : Bool :=
  List.rec (motive := fun _ => Tree → Bool) (fun _ => true)
    (fun x _ ih t => andB (rup t x) (ih (ins t x))) ps t

def replay (t : Tree) (ps : List Nat) : Tree :=
  List.rec (motive := fun _ => Tree → Tree) (fun t => t)
    (fun x _ ih t =>
      let t' := ins' t x
      seqT t' (ih t')) ps t

/-! ## Initial database and checkpoints -/

/-- The tautology `x₀ ∨ ¬x₀`, stored in slots without a clause. -/
def taut : Nat := 1 ||| (1 <<< 8192)

/-- Clause of `decodeLit` codes; a variable `≥ OFF` makes it the tautology. -/
def rawMask (c : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun k _ ih =>
      kif (k >>> 1).blt 8192 then
        (kif (k &&& 1).beq 0 then
          (kif k.beq 0 then ih ||| (1 <<< 8192) else ih ||| (1 <<< (k >>> 1)))
         else ih ||| (1 <<< ((k >>> 1) + 8192)))
      else ih ||| taut) c

/-- Insert tautologies under the given keys. -/
def shape (t : Tree) (keys : List Nat) : Tree :=
  List.rec (motive := fun _ => Tree → Tree) (fun t => t)
    (fun k _ ih t => let t' := insertF t k taut; seqT t' (ih t')) keys t

def loadRaw (t : Tree) (raw : List (List Nat)) (slots : List Nat) : Tree :=
  List.rec (motive := fun _ => Tree → List Nat → Tree) (fun t _ => t)
    (fun c _ ih t sl => List.rec (motive := fun _ => Tree) t
      (fun k rest _ => let t' := insertF t k (rawMask c); seqT t' (ih t' rest)) sl) raw t slots

/-- A checkpoint entry `key (lit+1) … (lit+1)` (no terminator needed). -/
def entC (x : Nat) : Nat := (litsL 255 0 (x >>> 13)).1

/-- Build a database from checkpoint entries. -/
def build (t : Tree) (es : List Nat) : Tree :=
  List.rec (motive := fun _ => Tree → Tree) (fun t => t)
    (fun x _ ih t => let t' := insertF t (x &&& 8191) (entC x); seqT t' (ih t')) es t

/-- Every checkpoint entry is in `t`. -/
def cpOk (t : Tree) (es : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => andB (lookB t (x &&& 8191) false (fun c => c.beq (entC x))) ih) es

/-- The empty clause is stored under key `k`. -/
def hasEmpty (t : Tree) (k : Nat) : Bool := lookB t k false (fun c => c.beq 0)

end

/-! ## Soundness -/

/-- Bit `b` is the literal `τ (b % 8192)`, negated if `b / 8192` is odd. -/
def bitTrue (τ : Nat → Bool) (b : Nat) : Bool := xor (τ (b % 8192)) ((b / 8192) % 2 == 1)

/-- Some literal of the clause `m` is true. -/
def MaskTrue (τ : Nat → Bool) (m : Nat) : Prop := ∃ b, m.testBit b = true ∧ bitTrue τ b = true

/-- All literals of `m` are false. -/
def AllFalse (τ : Nat → Bool) (m : Nat) : Prop := ∀ b, m.testBit b = true → bitTrue τ b = false

/-- All clauses of the tree are true.  (An inductive predicate, so that elaborating
`TreeTrue τ t` never evaluates `t`.) -/
inductive TreeTrue (τ : Nat → Bool) : Tree → Prop
  | nil : TreeTrue τ .nil
  | node {k c : Nat} {l r : Tree} : MaskTrue τ c → TreeTrue τ l → TreeTrue τ r →
      TreeTrue τ (.node k c l r)

theorem bitTrue_add (τ : Nat → Bool) (j : Nat) : bitTrue τ (j + 8192) = !bitTrue τ j := by
  unfold bitTrue
  have h1 : (j + 8192) % 8192 = j % 8192 := by omega
  have h2 : (j + 8192) / 8192 = j / 8192 + 1 := by omega
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one (j / 8192) with h | h
  · have : (j / 8192 + 1) % 2 = 1 := by omega
    rw [h, this]; cases τ (j % 8192) <;> rfl
  · have : (j / 8192 + 1) % 2 = 0 := by omega
    rw [h, this]; cases τ (j % 8192) <;> rfl

theorem bitTrue_sub (τ : Nat → Bool) (j : Nat) (hj : 8192 ≤ j) :
    bitTrue τ (j - 8192) = !bitTrue τ j := by
  have : j = (j - 8192) + 8192 := by omega
  conv => rhs; rw [this]
  rw [bitTrue_add, Bool.not_not]

theorem maskTrue_taut (τ : Nat → Bool) : MaskTrue τ taut := by
  cases h : τ 0
  · refine ⟨8192, ?_, ?_⟩
    · show (1 ||| (1 <<< 8192)).testBit 8192 = true
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]; simp
    · show xor (τ (8192 % 8192)) ((8192 / 8192) % 2 == 1) = true
      simp [h]
  · refine ⟨0, ?_, ?_⟩
    · show (1 ||| (1 <<< 8192)).testBit 0 = true
      rw [Nat.testBit_or]; simp
    · show xor (τ (0 % 8192)) ((0 / 8192) % 2 == 1) = true
      simp [h]

theorem maskTrue_or_left {τ : Nat → Bool} {a : Nat} (b : Nat) (h : MaskTrue τ a) :
    MaskTrue τ (a ||| b) := by
  obtain ⟨i, hi, ht⟩ := h
  exact ⟨i, by rw [Nat.testBit_or, hi]; rfl, ht⟩

theorem maskTrue_or_right {τ : Nat → Bool} (a : Nat) {b : Nat} (h : MaskTrue τ b) :
    MaskTrue τ (a ||| b) := by
  obtain ⟨i, hi, ht⟩ := h
  exact ⟨i, by rw [Nat.testBit_or, hi]; simp, ht⟩

theorem maskTrue_bit {τ : Nat → Bool} (i : Nat) (h : bitTrue τ i = true) : MaskTrue τ (1 <<< i) :=
  ⟨i, by rw [Nat.testBit_shiftLeft]; simp, h⟩

theorem not_maskTrue_zero (τ : Nat → Bool) : ¬ MaskTrue τ 0 := by
  rintro ⟨i, hi, _⟩; rw [Nat.zero_testBit] at hi; exact absurd hi (by decide)

/-! ### Trees -/

theorem lookB_spec {τ : Nat → Bool} (P : Bool → Prop) (k : Nat) (dflt : Bool) (f : Nat → Bool)
    (hd : P dflt) (hf : ∀ c, MaskTrue τ c → P (f c)) : ∀ t, TreeTrue τ t → P (lookB t k dflt f)
  | .nil, _ => hd
  | .node key c l r, .node hc hl hr => by
    show P (Bool.rec (Bool.rec (lookB r k dflt f) (f c) (k.beq key)) (lookB l k dflt f) (k.blt key))
    cases k.blt key
    · cases k.beq key
      · exact lookB_spec P k dflt f hd hf r hr
      · exact hf c hc
    · exact lookB_spec P k dflt f hd hf l hl

theorem lookT_const (k : Nat) (d : Tree) : ∀ t, lookT t k d (fun _ => d) = d
  | .nil => rfl
  | .node key c l r => by
    show Bool.rec (Bool.rec (lookT r k d (fun _ => d)) d (k.beq key)) (lookT l k d (fun _ => d))
      (k.blt key) = d
    rw [lookT_const k d l, lookT_const k d r]
    cases k.blt key <;> cases k.beq key <;> rfl

theorem setT_true {τ : Nat → Bool} (k c : Nat) (hc : MaskTrue τ c) :
    ∀ t, TreeTrue τ t → TreeTrue τ (setT t k c)
  | .nil, _ => .node hc .nil .nil
  | .node key c' l r, .node hc' hl hr => by
    show TreeTrue τ (Bool.rec (Bool.rec (Tree.node key c' l (setT r k c)) (Tree.node key c l r)
      (k.beq key)) (Tree.node key c' (setT l k c) r) (k.blt key))
    cases k.blt key
    · cases k.beq key
      · exact .node hc' hl (setT_true k c hc r hr)
      · exact .node hc hl hr
    · exact .node hc' (setT_true k c hc l hl) hr

theorem insertF_eq (t : Tree) (k c : Nat) : insertF t k c = setT t k c :=
  lookT_const k (setT t k c) (setT t k c)

theorem insertF'_eq (t : Tree) (k c : Nat) : insertF' t k c = setT t k c :=
  lookT_const k (setT' t k c) (setT' t k c)

theorem insertF_true {τ : Nat → Bool} {t : Tree} (k : Nat) {c : Nat} (ht : TreeTrue τ t)
    (hc : MaskTrue τ c) : TreeTrue τ (insertF t k c) := by
  rw [insertF_eq]; exact setT_true k c hc t ht

theorem seqT_eq (t r : Tree) : seqT t r = r := by cases t <;> rfl

/-! ### Unit propagation -/

theorem andB_eq_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

/-- A number whose bits are disjoint from those of its predecessor has at most one bit. -/
theorem single_bit : ∀ (u : Nat), (∀ i, (u.testBit i && (u - 1).testBit i) = false) →
    ∀ a b, u.testBit a = true → u.testBit b = true → a = b := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro hu a b ha hb
    rcases Nat.mod_two_eq_zero_or_one u with h | h
    · -- even: shift down
      have hu0 : u.testBit 0 = false := by rw [Nat.testBit_zero]; simp [h]
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := by
        cases a with
        | zero => rw [hu0] at ha; exact absurd ha (by decide)
        | succ a => exact ⟨a, rfl⟩
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := by
        cases b with
        | zero => rw [hu0] at hb; exact absurd hb (by decide)
        | succ b => exact ⟨b, rfl⟩
      have hpos : 0 < u := Nat.pos_of_ne_zero (by
        rintro rfl; rw [Nat.zero_testBit] at ha; exact absurd ha (by decide))
      have e1 : (u - 1) / 2 = u / 2 - 1 := by omega
      have hq : ∀ i, ((u / 2).testBit i && (u / 2 - 1).testBit i) = false := by
        intro i
        have := hu (i + 1)
        rw [Nat.testBit_succ, Nat.testBit_succ, e1] at this
        exact this
      rw [Nat.testBit_succ] at ha hb
      have := ih (u / 2) (by omega) hq a' b' ha hb
      omega
    · -- odd: no bit above 0
      have hz : ∀ i, u.testBit (i + 1) = false := by
        intro i
        have e1 : (u - 1) / 2 = u / 2 := by omega
        have := hu (i + 1)
        rw [Nat.testBit_succ, Nat.testBit_succ, e1, Bool.and_self] at this
        rw [Nat.testBit_succ]; exact this
      cases a with
      | succ a => rw [hz] at ha; exact absurd ha (by decide)
      | zero =>
        cases b with
        | succ b => rw [hz] at hb; exact absurd hb (by decide)
        | zero => rfl

theorem testBit_diff (d z i : Nat) :
    (d ^^^ (d &&& z)).testBit i = (d.testBit i && !z.testBit i) := by
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases d.testBit i <;> cases z.testBit i <;> rfl

theorem hstep_sound {τ : Nat → Bool} (ih : Nat → Nat → Bool)
    (hih : ∀ z x, AllFalse τ z → ih z x = true → False)
    (z x d : Nat) (hz : AllFalse τ z) (hd : MaskTrue τ d)
    (h : hstep ih z x (d ^^^ (d &&& z)) = true) : False := by
  obtain ⟨j, hdj, htj⟩ := hd
  -- the true literal `j` of `d` is not known false, so it is a bit of `u`
  have hzj : z.testBit j = false := by
    cases hzb : z.testBit j
    · rfl
    · have := hz j hzb; rw [htj] at this; exact absurd this (by decide)
  have huj : (d ^^^ (d &&& z)).testBit j = true := by rw [testBit_diff, hdj, hzj]; rfl
  revert h huj
  generalize d ^^^ (d &&& z) = u
  intro h huj
  have hst : hstep ih z x u = Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih z x)
        (ih (Bool.rec (motive := fun _ => Nat) (z ||| (u >>> 8192)) (z ||| (u <<< 8192))
          (u.blt (2 ^ 8192))) x) ((u &&& (u - 1)).beq 0)) true (u.beq 0) := rfl
  rw [hst] at h
  cases h0 : u.beq 0
  · rw [h0] at h
    cases h1 : (u &&& (u - 1)).beq 0
    · rw [h1] at h; exact hih z x hz h
    · rw [h1] at h
      have hsingle : ∀ i, u.testBit i = true → i = j := by
        intro i hi
        have hand : u &&& (u - 1) = 0 := Nat.eq_of_beq_eq_true h1
        exact single_bit u (fun k => by rw [← Nat.testBit_and, hand, Nat.zero_testBit]) i j hi huj
      cases h2 : u.blt (2 ^ 8192)
      · rw [h2] at h
        refine hih _ x ?_ h
        intro b hb
        rw [Nat.testBit_or] at hb
        rcases Bool.or_eq_true_iff.mp hb with hb | hb
        · exact hz b hb
        · rw [Nat.testBit_shiftRight] at hb
          have := hsingle _ hb
          have e : b = j - 8192 := by omega
          rw [e, bitTrue_sub τ j (by omega), htj]; rfl
      · rw [h2] at h
        refine hih _ x ?_ h
        intro b hb
        rw [Nat.testBit_or] at hb
        rcases Bool.or_eq_true_iff.mp hb with hb | hb
        · exact hz b hb
        · rw [Nat.testBit_shiftLeft, Bool.and_eq_true] at hb
          have hb1 : b ≥ 8192 := of_decide_eq_true hb.1
          have := hsingle _ hb.2
          have e : b = j + 8192 := by omega
          rw [e, bitTrue_add, htj]; rfl
  · -- conflict: every literal of `d` is known false
    have hu0 : u = 0 := Nat.eq_of_beq_eq_true h0
    rw [hu0, Nat.zero_testBit] at huj
    exact absurd huj (by decide)

theorem hints_sound {τ : Nat → Bool} {db : Tree} (hdb : TreeTrue τ db) :
    ∀ fuel z x, AllFalse τ z → hints db fuel z x = true → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro z x _ h
    rw [show hints db 0 z x = false from rfl] at h
    exact absurd h (by decide)
  | succ n ih =>
    intro z x hz h
    have key := lookB_spec (τ := τ) (fun b => AllFalse τ z → b = true → False) (x &&& 8191) false
      (fun d => hstep (hints db n) z (x >>> 13) (d ^^^ (d &&& z)))
      (fun _ h => absurd h (by decide))
      (fun c hc hz h => hstep_sound (hints db n) ih z (x >>> 13) c hz hc h) db hdb
    exact key hz h

theorem rup_sound {τ : Nat → Bool} {t : Tree} (ht : TreeTrue τ t) {x : Nat}
    (h : rup t x = true) : MaskTrue τ (lemC x) := by
  apply Classical.byContradiction
  intro hn
  have hz : AllFalse τ (lemC x) := by
    intro b hb
    cases hbt : bitTrue τ b
    · rfl
    · exact absurd ⟨b, hb, hbt⟩ hn
  exact hints_sound ht 4095 (lemC x) (lemH x) hz h

theorem replay_true (τ : Nat → Bool) {t : Tree} {ps : List Nat} (h : check t ps = true)
    (ht : TreeTrue τ t) : TreeTrue τ (replay t ps) := by
  induction ps generalizing t with
  | nil => exact ht
  | cons x xs ih =>
    have h' := andB_eq_true h
    have hins : TreeTrue τ (ins t x) := insertF_true _ ht (rup_sound ht h'.1)
    have e : replay t (x :: xs) = replay (ins t x) xs := by
      show seqT (ins' t x) (replay (ins' t x) xs) = _
      rw [seqT_eq]
      show replay (insertF' t (x &&& 8191) (lemC x)) xs = replay (insertF t (x &&& 8191) (lemC x)) xs
      rw [insertF_eq, insertF'_eq]
    rw [e]
    exact ih h'.2 hins

/-! ### Initial database, checkpoints, final conflict -/

theorem shape_true (τ : Nat → Bool) : ∀ (keys : List Nat) (t : Tree), TreeTrue τ t →
    TreeTrue τ (shape t keys)
  | [], _, ht => ht
  | k :: ks, t, ht => by
    show TreeTrue τ (seqT (insertF t k taut) (shape (insertF t k taut) ks))
    rw [seqT_eq]
    exact shape_true τ ks _ (insertF_true k ht (maskTrue_taut τ))

theorem decodeLit_even {k : Nat} (h : k % 2 = 0) : decodeLit k = ((k / 2 : Nat) : Int) := by
  unfold decodeLit; rw [if_pos h]; rfl

theorem decodeLit_odd {k : Nat} (h : k % 2 = 1) : decodeLit k = -((k / 2 : Nat) : Int) := by
  unfold decodeLit; rw [if_neg (by omega)]; rfl

theorem litTrue_ofNat (τ : Nat → Bool) (v : Nat) :
    litTrue τ (v : Int) = if v = 0 then !τ 0 else τ v := by
  unfold litTrue
  by_cases hv : v = 0
  · subst hv; simp
  · rw [if_pos (by omega), if_neg hv]; simp

theorem litTrue_negOfNat (τ : Nat → Bool) (v : Nat) : litTrue τ (-(v : Int)) = !τ v := by
  unfold litTrue; rw [if_neg (by omega)]; simp

theorem bitTrue_lt (τ : Nat → Bool) {v : Nat} (hv : v < 8192) : bitTrue τ v = τ v := by
  unfold bitTrue; rw [Nat.mod_eq_of_lt hv, Nat.div_eq_of_lt hv]; cases τ v <;> rfl

theorem rawMask_true (τ : Nat → Bool) : ∀ (c : List Nat),
    (c.map decodeLit).any (litTrue τ) = true → MaskTrue τ (rawMask c)
  | [], h => by simp at h
  | k :: ks, h => by
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true] at h
    have hs : k >>> 1 = k / 2 := by rw [Nat.shiftRight_eq_div_pow]
    have hand : k &&& 1 = k % 2 := Nat.and_one_is_mod k
    show MaskTrue τ (Bool.rec (motive := fun _ => Nat) (rawMask ks ||| taut)
      (Bool.rec (motive := fun _ => Nat) (rawMask ks ||| (1 <<< ((k >>> 1) + 8192)))
        (Bool.rec (motive := fun _ => Nat) (rawMask ks ||| (1 <<< (k >>> 1)))
          (rawMask ks ||| (1 <<< 8192)) (k.beq 0)) ((k &&& 1).beq 0)) ((k >>> 1).blt 8192))
    rw [hs, hand]
    rcases h with h | h
    · cases hb : (k / 2).blt 8192
      · exact maskTrue_or_right _ (maskTrue_taut τ)
      · have hk : k / 2 < 8192 := by rw [← Nat.blt_eq]; exact hb
        rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
        · rw [decodeLit_even h2, litTrue_ofNat] at h
          have e0 : (k % 2).beq 0 = true := by rw [h2]; rfl
          rw [e0]
          cases hk0 : k.beq 0
          · have hne : k / 2 ≠ 0 := by
              intro e
              have : k = 0 := by omega
              rw [this] at hk0; exact absurd hk0 (by decide)
            rw [if_neg hne] at h
            show MaskTrue τ (rawMask ks ||| (1 <<< (k / 2)))
            exact maskTrue_or_right _ (maskTrue_bit _ (by rw [bitTrue_lt τ hk]; exact h))
          · have e : k = 0 := Nat.eq_of_beq_eq_true hk0
            subst e
            simp at h
            show MaskTrue τ (rawMask ks ||| (1 <<< 8192))
            refine maskTrue_or_right _ (maskTrue_bit _ ?_)
            rw [show (8192 : Nat) = 0 + 8192 from rfl, bitTrue_add, bitTrue_lt τ (by decide), h]
            rfl
        · rw [decodeLit_odd h2, litTrue_negOfNat] at h
          have e0 : (k % 2).beq 0 = false := by rw [h2]; rfl
          rw [e0]
          show MaskTrue τ (rawMask ks ||| (1 <<< (k / 2 + 8192)))
          exact maskTrue_or_right _ (maskTrue_bit _ (by rw [bitTrue_add, bitTrue_lt τ hk]; exact h))
    · have hm := rawMask_true τ ks h
      cases (k / 2).blt 8192 <;> cases (k % 2).beq 0 <;> cases k.beq 0 <;>
        exact maskTrue_or_left _ hm

theorem loadRaw_true (τ : Nat → Bool) : ∀ (raw : List (List Nat)) (slots : List Nat) (t : Tree),
    (raw.map (·.map decodeLit)).all (clauseTrue τ) = true → TreeTrue τ t →
    TreeTrue τ (loadRaw t raw slots)
  | [], _, _, _, ht => ht
  | _ :: _, [], _, _, ht => ht
  | c :: cs, k :: ks, t, h, ht => by
    show TreeTrue τ (seqT (insertF t k (rawMask c)) (loadRaw (insertF t k (rawMask c)) cs ks))
    rw [seqT_eq]
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at h
    exact loadRaw_true τ cs ks _ h.2 (insertF_true k ht (rawMask_true τ c h.1))

theorem start_true (τ : Nat → Bool) {raw : List (List Nat)} {keys slots : List Nat}
    (h : cnfTrue τ (raw.map (·.map decodeLit)) = true) :
    TreeTrue τ (loadRaw (shape .nil keys) raw slots) :=
  loadRaw_true τ raw slots _ h (shape_true τ keys .nil .nil)

theorem build_true (τ : Nat → Bool) {R : Tree} (hR : TreeTrue τ R) :
    ∀ (es : List Nat) (t : Tree), cpOk R es = true → TreeTrue τ t → TreeTrue τ (build t es)
  | [], _, _, ht => ht
  | x :: xs, t, h, ht => by
    have h' := andB_eq_true h
    have hx : MaskTrue τ (entC x) :=
      lookB_spec (τ := τ) (fun b => b = true → MaskTrue τ (entC x)) (x &&& 8191) false
        (fun c => c.beq (entC x)) (fun h => absurd h (by decide))
        (fun c hc h => (Nat.eq_of_beq_eq_true h) ▸ hc) R hR h'.1
    show TreeTrue τ (seqT (insertF t (x &&& 8191) (entC x))
      (build (insertF t (x &&& 8191) (entC x)) xs))
    rw [seqT_eq]
    exact build_true τ hR xs _ h'.2 (insertF_true _ ht hx)

theorem cp_true (τ : Nat → Bool) {s : Tree} {ps cp keys : List Nat}
    (h : andB (check s ps) (cpOk (replay s ps) cp) = true) (hs : TreeTrue τ s) :
    TreeTrue τ (build (shape .nil keys) cp) :=
  build_true τ (replay_true τ (andB_eq_true h).1 hs) cp _ (andB_eq_true h).2
    (shape_true τ keys .nil .nil)

theorem final_false (τ : Nat → Bool) {s : Tree} {ps : List Nat} {k : Nat}
    (h : andB (check s ps) (hasEmpty (replay s ps) k) = true) (hs : TreeTrue τ s) : False :=
  lookB_spec (τ := τ) (fun b => b = true → False) k false (fun c => c.beq 0)
    (fun h => absurd h (by decide))
    (fun c hc h => not_maskTrue_zero τ ((Nat.eq_of_beq_eq_true h) ▸ hc))
    (replay s ps) (replay_true τ (andB_eq_true h).1 hs) (andB_eq_true h).2

theorem unsat_of_raw {raw : List (List Nat)}
    (h : ∀ τ, cnfTrue τ (raw.map (·.map decodeLit)) = true → False) :
    Unsat (raw.map (·.map decodeLit)) := by
  intro τ
  cases hc : cnfTrue τ (raw.map (·.map decodeLit))
  · rfl
  · exact absurd (h τ hc) id

end Snake9.Lrat144

#print axioms Snake9.Lrat144.rawMask_true
#print axioms Snake9.Lrat144.start_true
