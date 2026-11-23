import LratV3
/-!
# Segmented (checkpoint) LRAT replay for checker v3

A refutation too big for one module is cut into *pieces*. Piece `i` is replayed by `LratV3` on its own
proof list `Ps = B ++ own`, where `B` (the *boundary in*) holds, as lemma words, the clauses of earlier
pieces that piece `i` cites, and `own` its own segments. The boundary segments are not checked: their
truth is the hypothesis of the piece, `SegsTrue … B B.length`, which `segsTrue_append` lifts to
`SegsTrue … Ps B.length`; `LratV3.seg_step` then checks the own segments. The piece concludes the truth of
the next boundary `B'` (`SegsTrue … B' B'.length`) by `coverChk`: every word of `B'` has a reference (as
in `LratV3.resolve`) whose clause equals the word's clause. The last piece instead ends in the empty
clause (`LratV3.final_false`).

So a piece never evaluates another piece's proof data: its kernel work and memory are those of its own
segments, its boundary and the input clauses it cites. As in `LratV3`, nothing about the references or the
boundary data needs to be trusted: a wrong reference only makes `coverChk` fail.
-/

namespace Snake9.LratChain

open Snake9.LratV3

noncomputable section

local macro "kif " c:term " then " t:term " else " e:term : term =>
  `(Bool.rec (motive := fun _ => _) $e $t $c)

/-! ## Index lemmas for `List (List Nat)` (as `LratV3.nthN_eq`) -/

theorem tailR_eq : ∀ l : List (List Nat), tailR l = l.drop 1
  | [] => rfl
  | _ :: _ => rfl

theorem dropR_eq (l : List (List Nat)) : ∀ n, dropR l n = l.drop n
  | 0 => rfl
  | n + 1 => by
    show tailR (dropR l n) = l.drop (n + 1)
    rw [tailR_eq, dropR_eq l n, List.drop_drop]
    all_goals (congr 1 <;> omega)

theorem drop64R_eq (l : List (List Nat)) : ∀ h, drop64R l h = l.drop (64 * h)
  | 0 => rfl
  | h + 1 => by
    show dropR (drop64R l h) 64 = _
    rw [dropR_eq, drop64R_eq l h, List.drop_drop]
    all_goals (congr 1 <;> omega)

theorem nthR_eq (l : List (List Nat)) (j : Nat) : nthR l j = l.drop j := by
  rw [nthR_def, dropR_eq, drop64R_eq, List.drop_drop]
  congr 1
  rw [show Nat.shiftRight j 6 = j >>> 6 from rfl, show Nat.land j 63 = j &&& 63 from rfl,
    Nat.shiftRight_eq_div_pow, show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem segP_eq (Ps : List (List Nat)) (c : Nat) : segP Ps c = (Ps.drop c).headD [] := by
  show List.rec (motive := fun _ => List Nat) [] (fun p _ _ => p) (nthR Ps c) = _
  rw [nthR_eq]; cases Ps.drop c <;> rfl

theorem segP_append (Q R : List (List Nat)) {s : Nat} (hs : s < Q.length) :
    segP (Q ++ R) s = segP Q s := by
  rw [segP_eq, segP_eq, List.drop_append_of_le_length (Nat.le_of_lt hs)]
  obtain ⟨x, xs, hx⟩ : ∃ x xs, Q.drop s = x :: xs := by
    cases h : Q.drop s with
    | nil => exact absurd (List.drop_eq_nil_iff.mp h) (by omega)
    | cons x xs => exact ⟨x, xs, rfl⟩
  rw [hx]; rfl

/-- The boundary segments of a piece are true in `Ps = B ++ own` when they are true in `B`. -/
theorem segsTrue_append {OFF W M : Nat} {τ : Nat → Bool} (B R : List (List Nat))
    (h : SegsTrue OFF W M τ B B.length) : SegsTrue OFF W M τ (B ++ R) B.length := by
  intro s hs x hx
  rw [segP_append B R hs] at hx
  exact h s hs x hx

theorem segsTrue_nil (OFF W M : Nat) (τ : Nat → Bool) : SegsTrue OFF W M τ [] ([] : List (List Nat)).length :=
  segsTrue_zero OFF W M τ []

/-- A boundary is true segment by segment (each segment proved by its own `zipChk`, so that one
declaration decodes only the segment its references point into). -/
theorem segsTrue_cons {OFF W M : Nat} {τ : Nat → Bool} {q : List Nat} {Q : List (List Nat)}
    (hq : ∀ x ∈ q, MaskTrue OFF τ (lemC W M x)) (hQ : SegsTrue OFF W M τ Q Q.length) :
    SegsTrue OFF W M τ (q :: Q) (q :: Q).length := by
  intro s hs x hx
  cases s with
  | zero => exact hq x (by rw [segP_eq] at hx; simpa using hx)
  | succ s =>
    have hs' : s < Q.length := by simp at hs; omega
    apply hQ s hs' x
    rw [segP_eq] at hx ⊢
    simpa using hx

/-! ## The next boundary -/

/-- Every word of `xs` has the clause of the parallel reference in `rs` (references of `resolve` in
segment `n` of `Ps`; the lists must have the same length). -/
def zipChk (OFF W M : Nat) (raw : List (List Nat)) (Ps : List (List Nat)) (n : Nat) (xs : List Nat) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun rs => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) rs)
    (fun x _ ih rs => List.rec (motive := fun _ => Bool) false
      (fun r rs' _ => andB (Nat.beq (lemC W M x) (resolve OFF W M raw Ps n r)) (ih rs')) rs) xs

/-- `zipChk` for every segment of `Q` with the parallel reference list of `Rs`. -/
def coverChk (OFF W M : Nat) (raw : List (List Nat)) (Ps : List (List Nat)) (n : Nat)
    (Q : List (List Nat)) : List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun Rs => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Rs)
    (fun q _ ih Rs => List.rec (motive := fun _ => Bool) false
      (fun rr Rs' _ => andB (zipChk OFF W M raw Ps n q rr) (ih Rs')) Rs) Q

section
variable {OFF : Nat} (hoff : 0 < OFF) {τ : Nat → Bool}
include hoff

theorem zipChk_sound {W M : Nat} {raw : List (List Nat)} {Ps : List (List Nat)} {n : Nat}
    (hraw : RawTrue OFF τ raw) (hP : SegsTrue OFF W M τ Ps n) :
    ∀ (xs rs : List Nat), zipChk OFF W M raw Ps n xs rs = true → ∀ x ∈ xs, MaskTrue OFF τ (lemC W M x)
  | [], _, _ => fun _ hx => by cases hx
  | x :: xs, [], h => absurd h (by show ¬ (false = true); decide)
  | x :: xs, r :: rs, h => by
    have h' := andB_eq_true (show andB (Nat.beq (lemC W M x) (resolve OFF W M raw Ps n r))
      (zipChk OFF W M raw Ps n xs rs) = true from h)
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [Nat.eq_of_beq_eq_true h'.1]; exact resolve_true hoff hraw hP r
    · exact zipChk_sound hraw hP xs rs h'.2 y hy

theorem coverChk_sound {W M : Nat} {raw : List (List Nat)} {Ps : List (List Nat)} {n : Nat}
    (hraw : RawTrue OFF τ raw) (hP : SegsTrue OFF W M τ Ps n) :
    ∀ (Q Rs : List (List Nat)), coverChk OFF W M raw Ps n Q Rs = true → SegsTrue OFF W M τ Q Q.length
  | [], _, _ => segsTrue_zero _ _ _ _ _
  | q :: Q, [], h => absurd h (by show ¬ (false = true); decide)
  | q :: Q, rr :: Rs, h => by
    have h' := andB_eq_true (show andB (zipChk OFF W M raw Ps n q rr) (coverChk OFF W M raw Ps n Q Rs) = true from h)
    have hq := zipChk_sound hoff hraw hP q rr h'.1
    have hQ := coverChk_sound hraw hP Q Rs h'.2
    intro s hs x hx
    cases s with
    | zero => exact hq x (by rw [segP_eq] at hx; simpa using hx)
    | succ s =>
      have hs' : s < Q.length := by simp at hs; omega
      apply hQ s hs' x
      rw [segP_eq] at hx ⊢
      simpa using hx

end

end

end Snake9.LratChain
