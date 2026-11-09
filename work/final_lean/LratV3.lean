import LocalWindowModel

/-!
# LRAT checking without a clause database (checker v3)

The checkers `LratCheck`, `LratFast`, `LratFast2` keep the clause database in a binary search
tree.  Kernel profiles (milestones/26-replay-efficiency, section "Checker v3") show that most
of their kernel time is spent on that tree: building the start database of every segment
(`loadRaw`, `build`), inserting the lemmas of a segment and looking them up, and replaying
earlier segments to obtain the next start database.  Unit propagation itself is a small part.

Here there is no database.  Every clause is addressed by where it was *written*:

* an input clause by its index in the core `raw`;
* a lemma by its segment and its index in that segment's proof list.

A segment `c` (0-based) of the proof is the list `segP Ps c` of lemma words (lowest `W`-bit
word first) `n lit₁ … litₙ hint … hint 0`, a literal word being its bit position.  A hint word
`w` is

* `w ≥ FLAG`: entry `w - FLAG` of the segment's reference table `T` (chunks `tw + 2^6 st` of
  1024 fields of `tw` bits, `fieldT`; entry 0 is unused).  A reference `r` names
  the input clause `r >>> 12` if `r &&& 4095 = 0`, else lemma `r >>> 12` of segment
  `(r &&& 4095) - 1`, which must be an earlier segment;
* `1 ≤ w < FLAG`: lemma `w - 1` of the current segment, which must be an earlier lemma;
* `0`: the end of the hints.

Lookups go through `Nat.rec` on the hint word (as `LratFast2.getS`), so the kernel evaluates
each referenced clause once per declaration and finds it in its cache afterwards.  Lists are
indexed by two-level drops (`nthN`, `nthR`: 64 elements per step), written so that every
intermediate tail is a term with literal arguments that the kernel caches, and no evaluation
recurses deeply.

**Soundness needs no relation between the tables and the proof.** Whatever a reference or a
hint word says, the looked-up clause is an input clause, a lemma of an earlier segment, an
earlier lemma of the current segment, or the tautology `x₀ ∨ ¬x₀`; all of these are true
(`resolve_true`, `getE_true`, `getL_true`).  Out-of-range references give the tautology.  So the reference tables are
unchecked data, like the hints.  The segment theorems chain by induction on the segment
(`seg_step`), and the last segment must contain the empty clause (`final_false`).

Literals are bits of a `Nat` with offset `OFF` (variable `v < OFF` is bit `v`, `¬v` is bit
`v + OFF`); `OFF`, `W`, `M = 2^W - 1` and `FLAG` are arguments (literals at the call site), so
one module serves every window.  Kernel-evaluated functions use recursors and kernel-accelerated
`Nat` primitives only.
-/

namespace Snake9.LratV3

open Snake9.LocalWindow

noncomputable section

/-- Kernel branch `if c then t else e`, written with `Bool.rec`. -/
local macro "kif " c:term " then " t:term " else " e:term : term =>
  `(Bool.rec (motive := fun _ => _) $e $t $c)

/-- The tautology `x₀ ∨ ¬x₀`. -/
def taut (OFF : Nat) : Nat := Nat.lor 1 (Nat.shiftLeft 1 OFF)

def andB (a b : Bool) : Bool := kif a then b else false

/-! ## Indexed lists -/

def tailN (l : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) l
def tailR (l : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) [] (fun _ t _ => t) l

def dropN (l : List Nat) (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) l (fun _ ih => tailN ih) n
def dropR (l : List (List Nat)) (n : Nat) : List (List Nat) :=
  Nat.rec (motive := fun _ => List (List Nat)) l (fun _ ih => tailR ih) n

/-- `l` without its first `64 h` elements (each step is cached). -/
def drop64N (l : List Nat) (h : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) l (fun _ ih => dropN ih 64) h
def drop64R (l : List (List Nat)) (h : Nat) : List (List Nat) :=
  Nat.rec (motive := fun _ => List (List Nat)) l (fun _ ih => dropR ih 64) h

/-- `l` without its first `j` elements: `dropN (drop64N l (j >>> 6)) (j &&& 63)`, written so that
the inner term is `drop64N l (Nat.succ m)` with a literal `m`, which the kernel caches for all `j`
of the same block. -/
def nthN (l : List Nat) (j : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun lo => dropN l lo)
    (fun m _ lo => dropN (drop64N l (Nat.succ m)) lo) (Nat.shiftRight j 6) (Nat.land j 63)
def nthR (l : List (List Nat)) (j : Nat) : List (List Nat) :=
  Nat.rec (motive := fun _ => Nat → List (List Nat)) (fun lo => dropR l lo)
    (fun m _ lo => dropR (drop64R l (Nat.succ m)) lo) (Nat.shiftRight j 6) (Nat.land j 63)

/-- The proof list of segment `c`. -/
def segP (Ps : List (List Nat)) (c : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun p _ _ => p) (nthR Ps c)

/-! ## Clauses -/

/-- Read `n` literal words (bit positions): returns the clause and the remaining words. -/
def litsN (W M : Nat) (n : Nat) : Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun c x => (c, x))
    (fun _ ih c x => ih (Nat.lor c (Nat.shiftLeft 1 (Nat.land x M))) (Nat.shiftRight x W)) n

/-- The clause of a lemma word `n lit … lit hint … hint 0` and its hint words. -/
def lemC (W M x : Nat) : Nat := (litsN W M (Nat.land x M) 0 (Nat.shiftRight x W)).1
def lemH (W M x : Nat) : Nat := (litsN W M (Nat.land x M) 0 (Nat.shiftRight x W)).2

/-- Clause of `decodeLit` codes; a variable `≥ OFF` makes it the tautology. -/
def rawMask (OFF : Nat) (c : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun k _ ih =>
      kif Nat.ble (Nat.succ (Nat.shiftRight k 1)) OFF then
        (kif Nat.beq (Nat.land k 1) 0 then
          (kif Nat.beq k 0 then Nat.lor ih (Nat.shiftLeft 1 OFF)
           else Nat.lor ih (Nat.shiftLeft 1 (Nat.shiftRight k 1)))
         else Nat.lor ih (Nat.shiftLeft 1 (Nat.add (Nat.shiftRight k 1) OFF)))
      else Nat.lor ih (taut OFF)) c

/-- First input clause of `l` (the tautology if `l` is empty). -/
def headR (OFF : Nat) (l : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (taut OFF) (fun c _ _ => rawMask OFF c) l

/-- First lemma clause of `l` (the tautology if `l` is empty). -/
def headL (OFF W M : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (taut OFF) (fun x _ _ => lemC W M x) l

/-! ## Lookups -/

/-- The clause of reference `r` in segment `c`: input clause `r >>> 12` if `r &&& 4095 = 0`,
else lemma `r >>> 12` of segment `(r &&& 4095) - 1` if that is below `c`, else the tautology. -/
def resolve (OFF W M : Nat) (raw : List (List Nat)) (Ps : List (List Nat)) (c r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun j => headR OFF (nthR raw j))
    (fun m _ j => kif Nat.ble (Nat.succ m) c then headL OFF W M (nthN (segP Ps m) j) else taut OFF)
    (Nat.land r 4095) (Nat.shiftRight r 12)

/-- Field `j` of a table chunk `tw + 2^6 st` (fields of `tw` bits, lowest first). -/
def fieldT (ch j : Nat) : Nat :=
  Nat.land (Nat.shiftRight ch (Nat.add 6 (Nat.mul j (Nat.land ch 63))))
    (Nat.sub (Nat.shiftLeft 1 (Nat.land ch 63)) 1)

/-- The clause of the table entry `e`: the reference in field `e % 1024` of chunk `e / 1024`. -/
def lookE (OFF W M : Nat) (raw : List (List Nat)) (Ps : List (List Nat)) (T : List Nat) (c e : Nat) :
    Nat :=
  resolve OFF W M raw Ps c
    (fieldT (List.rec (motive := fun _ => Nat) 0 (fun ch _ _ => ch) (nthN T (Nat.shiftRight e 10)))
      (Nat.land e 1023))

/-- `lookE … e` through a term that depends only on the value of `e` (cached by the kernel). -/
def getE (OFF W M : Nat) (raw : List (List Nat)) (Ps : List (List Nat)) (T : List Nat) (c e : Nat) :
    Nat :=
  Nat.rec (motive := fun _ => Nat) (taut OFF)
    (fun m _ => Nat.add 0 (lookE OFF W M raw Ps T c (Nat.succ m))) e

/-- Lemma `j - 1` of the current segment `P` (cached per `j`). -/
def getL (OFF W M : Nat) (P : List Nat) (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (taut OFF)
    (fun m _ => Nat.add 0 (headL OFF W M (nthN P m))) j

/-! ## Unit propagation -/

/-- After looking up a hint clause: `u` are its literals not known to be false. -/
def hstep (OFF : Nat) (ih : Nat → Nat → Bool) (z x u : Nat) : Bool :=
  kif Nat.beq u 0 then true else
  kif Nat.beq (Nat.land u (Nat.sub u 1)) 0 then
    ih (kif Nat.ble (Nat.shiftLeft 1 OFF) u then Nat.lor z (Nat.shiftRight u OFF)
        else Nat.lor z (Nat.shiftLeft u OFF)) x
  else ih z x

/-- Unit propagation over the hint words `x` of lemma `i` of segment `c`; `z` holds the
literals known false.  Returns `true` iff a conflict is reached. -/
def hints (OFF W M FLAG : Nat) (raw : List (List Nat)) (Ps : List (List Nat)) (T P : List Nat)
    (c i : Nat) (fuel : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih z x =>
      kif Nat.ble FLAG (Nat.land x M) then
        hstep OFF ih z (Nat.shiftRight x W)
          (Nat.xor (getE OFF W M raw Ps T c (Nat.sub (Nat.land x M) FLAG))
            (Nat.land (getE OFF W M raw Ps T c (Nat.sub (Nat.land x M) FLAG)) z))
      else kif Nat.ble (Nat.land x M) i then
        (kif Nat.beq (Nat.land x M) 0 then false else
          hstep OFF ih z (Nat.shiftRight x W)
            (Nat.xor (getL OFF W M P (Nat.land x M)) (Nat.land (getL OFF W M P (Nat.land x M)) z)))
      else false) fuel

def rup (OFF W M FLAG : Nat) (raw : List (List Nat)) (Ps : List (List Nat)) (T P : List Nat)
    (c i x : Nat) : Bool :=
  hints OFF W M FLAG raw Ps T P c i 4095 (lemC W M x) (lemH W M x)

/-- `b`, after evaluating `i` to a literal (so that the lemma index never becomes a long
chain of `Nat.succ`). -/
def seqN (i : Nat) (b : Bool) : Bool := Nat.rec (motive := fun _ => Bool) b (fun _ _ => b) i

/-- Check the lemmas `L` (lemma `i` first) of the segment `P`. -/
def checkL (OFF W M FLAG : Nat) (raw : List (List Nat)) (Ps : List (List Nat)) (T P : List Nat)
    (c : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => seqN i (andB (rup OFF W M FLAG raw Ps T P c i x) (ih (Nat.succ i)))) L

/-- Check segment `c` of `Ps` with the reference table `T`. -/
def check (OFF W M FLAG : Nat) (raw : List (List Nat)) (Ps : List (List Nat)) (T : List Nat)
    (c : Nat) : Bool :=
  checkL OFF W M FLAG raw Ps T (segP Ps c) c (segP Ps c) 0

/-- Some lemma of `L` is the empty clause. -/
def hasEmpty (W M : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x _ ih => kif Nat.beq (lemC W M x) 0 then true else ih) L

end

/-! ## Soundness -/

/-- Bit `b` is the literal `τ (b % OFF)`, negated if `b / OFF` is odd. -/
def bitTrue (OFF : Nat) (τ : Nat → Bool) (b : Nat) : Bool := xor (τ (b % OFF)) ((b / OFF) % 2 == 1)

/-- Some literal of the clause `m` is true. -/
def MaskTrue (OFF : Nat) (τ : Nat → Bool) (m : Nat) : Prop :=
  ∃ b, m.testBit b = true ∧ bitTrue OFF τ b = true

/-- All literals of `m` are false. -/
def AllFalse (OFF : Nat) (τ : Nat → Bool) (m : Nat) : Prop :=
  ∀ b, m.testBit b = true → bitTrue OFF τ b = false

section
variable {OFF : Nat} (hoff : 0 < OFF) {τ : Nat → Bool}
include hoff

theorem bitTrue_add (j : Nat) : bitTrue OFF τ (j + OFF) = !bitTrue OFF τ j := by
  unfold bitTrue
  have h1 : (j + OFF) % OFF = j % OFF := by simp
  have h2 : (j + OFF) / OFF = j / OFF + 1 := by
    rw [Nat.add_div_right _ hoff]
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one (j / OFF) with h | h
  · have : (j / OFF + 1) % 2 = 1 := by omega
    rw [h, this]; cases τ (j % OFF) <;> rfl
  · have : (j / OFF + 1) % 2 = 0 := by omega
    rw [h, this]; cases τ (j % OFF) <;> rfl

theorem bitTrue_sub (j : Nat) (hj : OFF ≤ j) : bitTrue OFF τ (j - OFF) = !bitTrue OFF τ j := by
  have : j = (j - OFF) + OFF := by omega
  conv => rhs; rw [this]
  rw [bitTrue_add hoff, Bool.not_not]

omit hoff in
theorem bitTrue_lt {v : Nat} (hv : v < OFF) : bitTrue OFF τ v = τ v := by
  unfold bitTrue; rw [Nat.mod_eq_of_lt hv, Nat.div_eq_of_lt hv]; cases τ v <;> rfl

theorem maskTrue_taut : MaskTrue OFF τ (taut OFF) := by
  have t0 : (taut OFF).testBit 0 = true := by
    show (Nat.lor 1 (Nat.shiftLeft 1 OFF)).testBit 0 = true
    rw [show Nat.lor 1 (Nat.shiftLeft 1 OFF) = 1 ||| (1 <<< OFF) from rfl, Nat.testBit_or]; simp
  have t1 : (taut OFF).testBit OFF = true := by
    show (Nat.lor 1 (Nat.shiftLeft 1 OFF)).testBit OFF = true
    rw [show Nat.lor 1 (Nat.shiftLeft 1 OFF) = 1 ||| (1 <<< OFF) from rfl, Nat.testBit_or,
      Nat.testBit_shiftLeft]; simp
  cases h : τ 0
  · refine ⟨OFF, t1, ?_⟩
    have e := bitTrue_add hoff (τ := τ) 0
    rw [Nat.zero_add] at e
    rw [e, bitTrue_lt hoff, h]; rfl
  · exact ⟨0, t0, by rw [bitTrue_lt hoff, h]⟩

end

theorem maskTrue_or_left {OFF : Nat} {τ : Nat → Bool} {a : Nat} (b : Nat) (h : MaskTrue OFF τ a) :
    MaskTrue OFF τ (Nat.lor a b) := by
  obtain ⟨i, hi, ht⟩ := h
  exact ⟨i, by rw [show Nat.lor a b = a ||| b from rfl, Nat.testBit_or, hi]; rfl, ht⟩

theorem maskTrue_or_right {OFF : Nat} {τ : Nat → Bool} (a : Nat) {b : Nat} (h : MaskTrue OFF τ b) :
    MaskTrue OFF τ (Nat.lor a b) := by
  obtain ⟨i, hi, ht⟩ := h
  exact ⟨i, by rw [show Nat.lor a b = a ||| b from rfl, Nat.testBit_or, hi]; simp, ht⟩

theorem maskTrue_bit {OFF : Nat} {τ : Nat → Bool} (i : Nat) (h : bitTrue OFF τ i = true) :
    MaskTrue OFF τ (Nat.shiftLeft 1 i) :=
  ⟨i, by rw [show Nat.shiftLeft 1 i = 1 <<< i from rfl, Nat.testBit_shiftLeft]; simp, h⟩

theorem not_maskTrue_zero {OFF : Nat} (τ : Nat → Bool) : ¬ MaskTrue OFF τ 0 := by
  rintro ⟨i, hi, _⟩; rw [Nat.zero_testBit] at hi; exact absurd hi (by decide)

theorem andB_eq_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

/-! ### Lists -/

theorem tailN_sub {P : Nat → Prop} : ∀ {l : List Nat}, (∀ x ∈ l, P x) → ∀ x ∈ tailN l, P x
  | [], _ => fun _ h => by cases h
  | _ :: _, h => fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem tailR_sub {P : List Nat → Prop} :
    ∀ {l : List (List Nat)}, (∀ x ∈ l, P x) → ∀ x ∈ tailR l, P x
  | [], _ => fun _ h => by cases h
  | _ :: _, h => fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem dropN_sub {P : Nat → Prop} {l : List Nat} (h : ∀ x ∈ l, P x) :
    ∀ n, ∀ x ∈ dropN l n, P x
  | 0 => h
  | n + 1 => tailN_sub (dropN_sub h n)

theorem dropR_sub {P : List Nat → Prop} {l : List (List Nat)} (h : ∀ x ∈ l, P x) :
    ∀ n, ∀ x ∈ dropR l n, P x
  | 0 => h
  | n + 1 => tailR_sub (dropR_sub h n)

theorem drop64N_sub {P : Nat → Prop} {l : List Nat} (h : ∀ x ∈ l, P x) :
    ∀ n, ∀ x ∈ drop64N l n, P x
  | 0 => h
  | n + 1 => dropN_sub (drop64N_sub h n) 64

theorem drop64R_sub {P : List Nat → Prop} {l : List (List Nat)} (h : ∀ x ∈ l, P x) :
    ∀ n, ∀ x ∈ drop64R l n, P x
  | 0 => h
  | n + 1 => dropR_sub (drop64R_sub h n) 64

theorem nthN_def (l : List Nat) (j : Nat) :
    nthN l j = dropN (drop64N l (Nat.shiftRight j 6)) (Nat.land j 63) := by
  show Nat.rec (motive := fun _ => Nat → List Nat) (fun lo => dropN l lo)
    (fun m _ lo => dropN (drop64N l (Nat.succ m)) lo) (Nat.shiftRight j 6) (Nat.land j 63) = _
  cases Nat.shiftRight j 6 <;> rfl

theorem nthR_def (l : List (List Nat)) (j : Nat) :
    nthR l j = dropR (drop64R l (Nat.shiftRight j 6)) (Nat.land j 63) := by
  show Nat.rec (motive := fun _ => Nat → List (List Nat)) (fun lo => dropR l lo)
    (fun m _ lo => dropR (drop64R l (Nat.succ m)) lo) (Nat.shiftRight j 6) (Nat.land j 63) = _
  cases Nat.shiftRight j 6 <;> rfl

theorem nthN_sub {P : Nat → Prop} {l : List Nat} (h : ∀ x ∈ l, P x) (j : Nat) :
    ∀ x ∈ nthN l j, P x := by
  rw [nthN_def]; exact dropN_sub (drop64N_sub h _) _

theorem nthR_sub {P : List Nat → Prop} {l : List (List Nat)} (h : ∀ x ∈ l, P x) (j : Nat) :
    ∀ x ∈ nthR l j, P x := by
  rw [nthR_def]; exact dropR_sub (drop64R_sub h _) _

theorem tailN_eq : ∀ l : List Nat, tailN l = l.drop 1
  | [] => rfl
  | _ :: _ => rfl

/-- `dropN l n` is `List.drop n l`. -/
theorem dropN_eq (l : List Nat) : ∀ n, dropN l n = l.drop n
  | 0 => rfl
  | n + 1 => by
    show tailN (dropN l n) = l.drop (n + 1)
    rw [tailN_eq, dropN_eq l n, List.drop_drop]
    all_goals (congr 1 <;> omega)

theorem drop64N_eq (l : List Nat) : ∀ h, drop64N l h = l.drop (64 * h)
  | 0 => rfl
  | h + 1 => by
    show dropN (drop64N l h) 64 = _
    rw [dropN_eq, drop64N_eq l h, List.drop_drop]
    all_goals (congr 1 <;> omega)

theorem nthN_eq (l : List Nat) (j : Nat) : nthN l j = l.drop j := by
  rw [nthN_def, dropN_eq, drop64N_eq, List.drop_drop]
  congr 1
  rw [show Nat.shiftRight j 6 = j >>> 6 from rfl, show Nat.land j 63 = j &&& 63 from rfl,
    Nat.shiftRight_eq_div_pow, show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-! ### Clauses and lookups -/

/-- All lemmas of the segments before `c` are true. -/
def SegsTrue (OFF W M : Nat) (τ : Nat → Bool) (Ps : List (List Nat)) (c : Nat) : Prop :=
  ∀ s, s < c → ∀ x ∈ segP Ps s, MaskTrue OFF τ (lemC W M x)

/-- All input clauses are true. -/
def RawTrue (OFF : Nat) (τ : Nat → Bool) (raw : List (List Nat)) : Prop :=
  ∀ c ∈ raw, MaskTrue OFF τ (rawMask OFF c)

section
variable {OFF : Nat} (hoff : 0 < OFF) {τ : Nat → Bool}
include hoff

theorem headR_true {l : List (List Nat)} (h : ∀ c ∈ l, MaskTrue OFF τ (rawMask OFF c)) :
    MaskTrue OFF τ (headR OFF l) := by
  cases l with
  | nil => exact maskTrue_taut hoff
  | cons c cs => exact h c (List.mem_cons_self)

theorem headL_true {W M : Nat} {l : List Nat} (h : ∀ x ∈ l, MaskTrue OFF τ (lemC W M x)) :
    MaskTrue OFF τ (headL OFF W M l) := by
  cases l with
  | nil => exact maskTrue_taut hoff
  | cons c cs => exact h c (List.mem_cons_self)

theorem resolve_true {W M : Nat} {raw : List (List Nat)} {Ps : List (List Nat)} {c : Nat}
    (hraw : RawTrue OFF τ raw) (hP : SegsTrue OFF W M τ Ps c) (r : Nat) :
    MaskTrue OFF τ (resolve OFF W M raw Ps c r) := by
  show MaskTrue OFF τ (Nat.rec (motive := fun _ => Nat → Nat) (fun j => headR OFF (nthR raw j))
    (fun m _ j => Bool.rec (taut OFF) (headL OFF W M (nthN (segP Ps m) j)) (Nat.ble (Nat.succ m) c))
    (Nat.land r 4095) (Nat.shiftRight r 12))
  cases Nat.land r 4095 with
  | zero => exact headR_true hoff (nthR_sub hraw _)
  | succ m =>
    show MaskTrue OFF τ (Bool.rec (taut OFF) (headL OFF W M (nthN (segP Ps m) (Nat.shiftRight r 12)))
      (Nat.ble (Nat.succ m) c))
    cases h1 : Nat.ble (Nat.succ m) c
    · exact maskTrue_taut hoff
    · exact headL_true hoff (nthN_sub (hP m (Nat.le_of_ble_eq_true h1)) _)

theorem getE_true {W M : Nat} {raw : List (List Nat)} {Ps : List (List Nat)} {T : List Nat}
    {c : Nat} (hraw : RawTrue OFF τ raw) (hP : SegsTrue OFF W M τ Ps c) :
    ∀ e, MaskTrue OFF τ (getE OFF W M raw Ps T c e)
  | 0 => maskTrue_taut hoff
  | m + 1 => by
    show MaskTrue OFF τ (Nat.add 0 (lookE OFF W M raw Ps T c (Nat.succ m)))
    rw [show Nat.add 0 (lookE OFF W M raw Ps T c (Nat.succ m)) = lookE OFF W M raw Ps T c (m + 1)
      from Nat.zero_add _]
    exact resolve_true hoff hraw hP _

/-- Lemma `j - 1` of `P`, for `1 ≤ j ≤ i`, when the first `i` lemmas of `P` are true. -/
theorem getL_true {W M : Nat} {P : List Nat} {i : Nat}
    (hi : ∀ x ∈ P.take i, MaskTrue OFF τ (lemC W M x)) :
    ∀ j, j ≤ i → MaskTrue OFF τ (getL OFF W M P j)
  | 0, _ => maskTrue_taut hoff
  | m + 1, hj => by
    show MaskTrue OFF τ (Nat.add 0 (headL OFF W M (nthN P m)))
    rw [show Nat.add 0 (headL OFF W M (nthN P m)) = headL OFF W M (nthN P m) from Nat.zero_add _,
      nthN_eq]
    show MaskTrue OFF τ (List.rec (motive := fun _ => Nat) (taut OFF) (fun x _ _ => lemC W M x)
      (P.drop m))
    cases hd : P.drop m with
    | nil => exact maskTrue_taut hoff
    | cons x xs =>
      apply hi
      have hx' : x ∈ P.take (m + 1) := by
        rw [List.take_succ, ← List.head?_drop, hd]; simp
      exact List.take_subset_take_left P (by omega : m + 1 ≤ i) hx'

end

/-! ### Unit propagation -/

/-- A number whose bits are disjoint from those of its predecessor has at most one bit. -/
theorem single_bit : ∀ (u : Nat), (∀ i, (u.testBit i && (u - 1).testBit i) = false) →
    ∀ a b, u.testBit a = true → u.testBit b = true → a = b := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro hu a b ha hb
    rcases Nat.mod_two_eq_zero_or_one u with h | h
    · have hu0 : u.testBit 0 = false := by rw [Nat.testBit_zero]; simp [h]
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
    · have hz : ∀ i, u.testBit (i + 1) = false := by
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
    (Nat.xor d (Nat.land d z)).testBit i = (d.testBit i && !z.testBit i) := by
  rw [show Nat.xor d (Nat.land d z) = d ^^^ (d &&& z) from rfl, Nat.testBit_xor, Nat.testBit_and]
  cases d.testBit i <;> cases z.testBit i <;> rfl

theorem hstep_sound {OFF : Nat} (hoff : 0 < OFF) {τ : Nat → Bool} (ih : Nat → Nat → Bool)
    (hih : ∀ z x, AllFalse OFF τ z → ih z x = true → False)
    (z x d : Nat) (hz : AllFalse OFF τ z) (hd : MaskTrue OFF τ d)
    (h : hstep OFF ih z x (Nat.xor d (Nat.land d z)) = true) : False := by
  obtain ⟨j, hdj, htj⟩ := hd
  have hzj : z.testBit j = false := by
    cases hzb : z.testBit j
    · rfl
    · have := hz j hzb; rw [htj] at this; exact absurd this (by decide)
  have huj : (Nat.xor d (Nat.land d z)).testBit j = true := by rw [testBit_diff, hdj, hzj]; rfl
  revert h huj
  generalize Nat.xor d (Nat.land d z) = u
  intro h huj
  have hst : hstep OFF ih z x u = Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih z x)
        (ih (Bool.rec (motive := fun _ => Nat) (Nat.lor z (Nat.shiftLeft u OFF))
          (Nat.lor z (Nat.shiftRight u OFF)) (Nat.ble (Nat.shiftLeft 1 OFF) u)) x)
        (Nat.beq (Nat.land u (Nat.sub u 1)) 0)) true (Nat.beq u 0) := rfl
  rw [hst] at h
  cases h0 : Nat.beq u 0
  · rw [h0] at h
    cases h1 : Nat.beq (Nat.land u (Nat.sub u 1)) 0
    · rw [h1] at h; exact hih z x hz h
    · rw [h1] at h
      have hsingle : ∀ i, u.testBit i = true → i = j := by
        intro i hi
        have hand : u &&& (u - 1) = 0 := Nat.eq_of_beq_eq_true h1
        exact single_bit u (fun k => by rw [← Nat.testBit_and, hand, Nat.zero_testBit]) i j hi huj
      cases h2 : Nat.ble (Nat.shiftLeft 1 OFF) u
      · -- `u < 2^OFF`: the literal `j < OFF` is positive, its negation is bit `j + OFF`
        rw [h2] at h
        have hlt : u < 2 ^ OFF := by
          have : ¬ (Nat.shiftLeft 1 OFF ≤ u) := fun hle => by
            rw [Nat.ble_eq_true_of_le hle] at h2; exact absurd h2 (by decide)
          rw [show Nat.shiftLeft 1 OFF = 1 <<< OFF from rfl, Nat.shiftLeft_eq, Nat.one_mul] at this
          omega
        have hjo : j < OFF := by
          apply Classical.byContradiction
          intro hn
          have : u.testBit j = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))
          rw [this] at huj; exact absurd huj (by decide)
        refine hih _ x ?_ h
        intro b hb
        rw [show Nat.lor z (Nat.shiftLeft u OFF) = z ||| (u <<< OFF) from rfl, Nat.testBit_or] at hb
        rcases Bool.or_eq_true_iff.mp hb with hb | hb
        · exact hz b hb
        · rw [Nat.testBit_shiftLeft, Bool.and_eq_true] at hb
          have hb1 : b ≥ OFF := of_decide_eq_true hb.1
          have := hsingle _ hb.2
          have e : b = j + OFF := by omega
          rw [e, bitTrue_add hoff, htj]; rfl
      · -- `u ≥ 2^OFF`: the literal `j ≥ OFF` is negative, its negation is bit `j - OFF`
        rw [h2] at h
        have hge : 2 ^ OFF ≤ u := by
          have := Nat.le_of_ble_eq_true h2
          rwa [show Nat.shiftLeft 1 OFF = 1 <<< OFF from rfl, Nat.shiftLeft_eq, Nat.one_mul] at this
        have hjo : OFF ≤ j := by
          apply Classical.byContradiction
          intro hn
          have hlt : u < 2 ^ OFF := by
            apply Nat.lt_pow_two_of_testBit
            intro i hi
            cases hb : u.testBit i
            · rfl
            · have := hsingle i hb; omega
          omega
        refine hih _ x ?_ h
        intro b hb
        rw [show Nat.lor z (Nat.shiftRight u OFF) = z ||| (u >>> OFF) from rfl, Nat.testBit_or] at hb
        rcases Bool.or_eq_true_iff.mp hb with hb | hb
        · exact hz b hb
        · rw [Nat.testBit_shiftRight] at hb
          have := hsingle _ hb
          have e : b = j - OFF := by omega
          rw [e, bitTrue_sub hoff j hjo, htj]; rfl
  · have hu0 : u = 0 := Nat.eq_of_beq_eq_true h0
    rw [hu0, Nat.zero_testBit] at huj
    exact absurd huj (by decide)

theorem hints_sound {OFF W M FLAG : Nat} (hoff : 0 < OFF) {τ : Nat → Bool}
    {raw : List (List Nat)} {Ps : List (List Nat)} {T P : List Nat} {c i : Nat}
    (hraw : RawTrue OFF τ raw) (hP : SegsTrue OFF W M τ Ps c)
    (hi : ∀ x ∈ P.take i, MaskTrue OFF τ (lemC W M x)) :
    ∀ fuel z x, AllFalse OFF τ z → hints OFF W M FLAG raw Ps T P c i fuel z x = true → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro z x _ h
    exact absurd h (by show ¬ (false = true); decide)
  | succ n ih =>
    intro z x hz h
    revert h
    show Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool)
            (hstep OFF (hints OFF W M FLAG raw Ps T P c i n) z (Nat.shiftRight x W)
              (Nat.xor (getL OFF W M P (Nat.land x M)) (Nat.land (getL OFF W M P (Nat.land x M)) z)))
            false (Nat.beq (Nat.land x M) 0))
          (Nat.ble (Nat.land x M) i))
        (hstep OFF (hints OFF W M FLAG raw Ps T P c i n) z (Nat.shiftRight x W)
          (Nat.xor (getE OFF W M raw Ps T c (Nat.sub (Nat.land x M) FLAG))
            (Nat.land (getE OFF W M raw Ps T c (Nat.sub (Nat.land x M) FLAG)) z)))
        (Nat.ble FLAG (Nat.land x M)) = true → False
    cases Nat.ble FLAG (Nat.land x M)
    · cases hl : Nat.ble (Nat.land x M) i
      · intro h; exact Bool.false_ne_true h
      · cases Nat.beq (Nat.land x M) 0
        · exact hstep_sound hoff _ ih z _ _ hz
            (getL_true hoff hi _ (Nat.le_of_ble_eq_true hl))
        · intro h; exact Bool.false_ne_true h
    · exact hstep_sound hoff _ ih z _ _ hz (getE_true hoff hraw hP _)

theorem rup_sound {OFF W M FLAG : Nat} (hoff : 0 < OFF) {τ : Nat → Bool}
    {raw : List (List Nat)} {Ps : List (List Nat)} {T P : List Nat} {c i x : Nat}
    (hraw : RawTrue OFF τ raw) (hP : SegsTrue OFF W M τ Ps c)
    (hi : ∀ y ∈ P.take i, MaskTrue OFF τ (lemC W M y))
    (h : rup OFF W M FLAG raw Ps T P c i x = true) : MaskTrue OFF τ (lemC W M x) := by
  apply Classical.byContradiction
  intro hn
  have hz : AllFalse OFF τ (lemC W M x) := by
    intro b hb
    cases hbt : bitTrue OFF τ b
    · rfl
    · exact absurd ⟨b, hb, hbt⟩ hn
  exact hints_sound hoff hraw hP hi 4095 _ _ hz h

theorem seqN_eq (i : Nat) (b : Bool) : seqN i b = b := by cases i <;> rfl

theorem checkL_sound {OFF W M FLAG : Nat} (hoff : 0 < OFF) {τ : Nat → Bool}
    {raw : List (List Nat)} {Ps : List (List Nat)} {T P : List Nat} {c : Nat}
    (hraw : RawTrue OFF τ raw) (hP : SegsTrue OFF W M τ Ps c) :
    ∀ (L : List Nat) (i : Nat), P.drop i = L → (∀ y ∈ P.take i, MaskTrue OFF τ (lemC W M y)) →
      checkL OFF W M FLAG raw Ps T P c L i = true → ∀ y ∈ P, MaskTrue OFF τ (lemC W M y)
  | [], i, hL, hi, _ => by
    intro y hy
    rw [← List.take_append_drop i P, hL, List.append_nil] at hy
    exact hi y hy
  | x :: xs, i, hL, hi, h => by
    have h' := andB_eq_true (show andB (rup OFF W M FLAG raw Ps T P c i x)
      (checkL OFF W M FLAG raw Ps T P c xs (Nat.succ i)) = true by
        rw [← seqN_eq i (andB _ _)]; exact h)
    have hx := rup_sound hoff hraw hP hi h'.1
    apply checkL_sound hoff hraw hP xs (i + 1)
    · rw [← List.drop_drop, hL]; rfl
    · intro y hy
      rw [List.take_succ] at hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hi y hy
      · have : P[i]? = some x := by
          rw [← List.head?_drop, hL]; rfl
        rw [this] at hy
        rw [Option.mem_toList, Option.mem_def, Option.some.injEq] at hy
        exact hy ▸ hx
    · exact h'.2

/-- One segment: if the lemmas of the segments before `c` are true and `check` accepts
segment `c`, the lemmas of the segments up to `c` are true. -/
theorem seg_step {OFF W M FLAG : Nat} (hoff : 0 < OFF) {τ : Nat → Bool}
    {raw : List (List Nat)} {Ps : List (List Nat)} {T : List Nat} {c : Nat}
    (hraw : RawTrue OFF τ raw) (h : check OFF W M FLAG raw Ps T c = true)
    (hP : SegsTrue OFF W M τ Ps c) : SegsTrue OFF W M τ Ps (c + 1) := by
  have hc := checkL_sound hoff hraw hP (segP Ps c) 0 rfl (by intro y hy; simp at hy) h
  intro s hs
  rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
  · exact hP s hs
  · exact hs ▸ hc

theorem segsTrue_zero (OFF W M : Nat) (τ : Nat → Bool) (Ps : List (List Nat)) :
    SegsTrue OFF W M τ Ps 0 := fun _ h => absurd h (Nat.not_lt_zero _)

/-- The last segment: it is accepted and contains the empty clause. -/
theorem final_false {OFF W M FLAG : Nat} (hoff : 0 < OFF) {τ : Nat → Bool}
    {raw : List (List Nat)} {Ps : List (List Nat)} {T : List Nat} {c : Nat}
    (hraw : RawTrue OFF τ raw)
    (h : andB (check OFF W M FLAG raw Ps T c) (hasEmpty W M (segP Ps c)) = true)
    (hP : SegsTrue OFF W M τ Ps c) : False := by
  have h' := andB_eq_true h
  have hs := seg_step hoff hraw h'.1 hP c (Nat.lt_succ_self c)
  have key : ∀ L : List Nat, (∀ x ∈ L, MaskTrue OFF τ (lemC W M x)) → hasEmpty W M L = true → False := by
    intro L
    induction L with
    | nil => intro _ h; exact absurd h (by show ¬ (false = true); decide)
    | cons x xs ih =>
      intro hL h
      revert h
      show Bool.rec (motive := fun _ => Bool) (hasEmpty W M xs) true (Nat.beq (lemC W M x) 0) = true → False
      cases he : Nat.beq (lemC W M x) 0
      · exact ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
      · intro _
        have := hL x (List.mem_cons_self)
        rw [Nat.eq_of_beq_eq_true he] at this
        exact not_maskTrue_zero τ this
  exact key _ hs h'.2

/-! ### Input clauses -/

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

theorem rawMask_true {OFF : Nat} (hoff : 0 < OFF) (τ : Nat → Bool) : ∀ (c : List Nat),
    (c.map decodeLit).any (litTrue τ) = true → MaskTrue OFF τ (rawMask OFF c)
  | [], h => by simp at h
  | k :: ks, h => by
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true] at h
    have hs : Nat.shiftRight k 1 = k / 2 := by
      rw [show Nat.shiftRight k 1 = k >>> 1 from rfl, Nat.shiftRight_eq_div_pow]; all_goals rfl
    have hand : Nat.land k 1 = k % 2 := Nat.and_one_is_mod k
    show MaskTrue OFF τ (Bool.rec (motive := fun _ => Nat) (Nat.lor (rawMask OFF ks) (taut OFF))
      (Bool.rec (motive := fun _ => Nat)
        (Nat.lor (rawMask OFF ks) (Nat.shiftLeft 1 (Nat.add (Nat.shiftRight k 1) OFF)))
        (Bool.rec (motive := fun _ => Nat) (Nat.lor (rawMask OFF ks) (Nat.shiftLeft 1 (Nat.shiftRight k 1)))
          (Nat.lor (rawMask OFF ks) (Nat.shiftLeft 1 OFF)) (Nat.beq k 0)) (Nat.beq (Nat.land k 1) 0))
      (Nat.ble (Nat.succ (Nat.shiftRight k 1)) OFF))
    rw [hs, hand]
    rcases h with h | h
    · cases hb : Nat.ble (Nat.succ (k / 2)) OFF
      · exact maskTrue_or_right _ (maskTrue_taut hoff)
      · have hk : k / 2 < OFF := Nat.le_of_ble_eq_true hb
        rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
        · rw [decodeLit_even h2, litTrue_ofNat] at h
          have e0 : Nat.beq (k % 2) 0 = true := by rw [h2]; rfl
          rw [e0]
          cases hk0 : Nat.beq k 0
          · have hne : k / 2 ≠ 0 := by
              intro e
              have : k = 0 := by omega
              rw [this] at hk0; exact absurd hk0 (by decide)
            rw [if_neg hne] at h
            show MaskTrue OFF τ (Nat.lor (rawMask OFF ks) (Nat.shiftLeft 1 (k / 2)))
            exact maskTrue_or_right _ (maskTrue_bit _ (by rw [bitTrue_lt hk]; exact h))
          · have e : k = 0 := Nat.eq_of_beq_eq_true hk0
            subst e
            simp at h
            show MaskTrue OFF τ (Nat.lor (rawMask OFF ks) (Nat.shiftLeft 1 OFF))
            refine maskTrue_or_right _ (maskTrue_bit _ ?_)
            have e := bitTrue_add hoff (τ := τ) 0
            rw [Nat.zero_add] at e
            rw [e, bitTrue_lt hoff, h]; rfl
        · rw [decodeLit_odd h2, litTrue_negOfNat] at h
          have e0 : Nat.beq (k % 2) 0 = false := by rw [h2]; rfl
          rw [e0]
          show MaskTrue OFF τ (Nat.lor (rawMask OFF ks) (Nat.shiftLeft 1 (Nat.add (k / 2) OFF)))
          exact maskTrue_or_right _ (maskTrue_bit _ (by
            rw [show Nat.add (k / 2) OFF = k / 2 + OFF from rfl, bitTrue_add hoff, bitTrue_lt hk]
            exact h))
    · have hm := rawMask_true hoff τ ks h
      cases Nat.ble (Nat.succ (k / 2)) OFF <;> cases Nat.beq (k % 2) 0 <;> cases Nat.beq k 0 <;>
        exact maskTrue_or_left _ hm

theorem rawTrue_of_cnf {OFF : Nat} (hoff : 0 < OFF) {τ : Nat → Bool} {raw : List (List Nat)}
    (h : cnfTrue τ (raw.map (·.map decodeLit)) = true) : RawTrue OFF τ raw := by
  intro c hc
  apply rawMask_true hoff τ c
  have := List.all_eq_true.mp h (c.map decodeLit) (List.mem_map_of_mem hc)
  exact this

theorem unsat_of_raw {raw : List (List Nat)}
    (h : ∀ τ, cnfTrue τ (raw.map (·.map decodeLit)) = true → False) :
    Unsat (raw.map (·.map decodeLit)) := by
  intro τ
  cases hc : cnfTrue τ (raw.map (·.map decodeLit))
  · rfl
  · exact absurd (h τ hc) id

end Snake9.LratV3
