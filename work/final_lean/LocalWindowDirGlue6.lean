import LocalWindowDirModel

/-!
# Mixed key lists: assembling the six-centre premise from proved certificate sets

The premise of the six-centre chain (`upper_of_refuted6`) is `AllRefutedList keys` for one
key list `keys` that mixes windows of 3 to 7 directions (2 to 6 centres).  Every key
`(ds, syms)` asks for `Refuted (winOf ds) (boundsOf syms)`.  This is the same statement,
with the same `winOf` and `boundsOf`, that the earlier certificate sets prove for their own
keys: `AllRefuted237 = AllRefutedList dirKeysR4b` (`LocalWindowDirUnsatR4b.allRefuted237`),
`AllRefuted236 = AllRefutedList dirKeysR4` (`LocalWindowDirUnsatR4.allRefuted236`), and so
on.  `Refuted` does not mention the ball radius or the number of centres (those only decide
which CNF certifies a key), so a four- or five-centre exclusion that is already proved is a
key of the six-centre list as it stands.  Nothing has to be converted; the only work is
list bookkeeping.

* `AllRefutedList.iff_forall`, `.of_forall`, `.append`, `.of_subset`: `AllRefutedList` is
  "every member is refuted".
* `AllRefutedSrcs srcs`: every list of `srcs` is all-refuted (a conjunction, one conjunct
  per source).
* `pickOK srcs keys ws`: a kernel-checkable witness that every key of `keys` occurs in some
  source: the `n`-th key comes with `ws[n] = (j, i)`, and the `i`-th entry of source `j`
  must equal it.  This costs one list walk and one key comparison per key, instead of a
  search through all sources.
* `allRefuted_of_pick`: from `AllRefutedSrcs srcs` and `pickOK srcs keys ws = true`, the
  premise `AllRefutedList keys` follows.
* `mergeOK` / `allRefuted_of_merge`: the same with one source tag per key, checked by a
  merge (linear in the total length; the form used for long key lists, see below).

Core Lean only.
-/

namespace Snake9.LocalWindow

/-- A certificate key: canonical direction list and lumped counts. -/
abbrev DirKey := List Nat × List Nat

theorem AllRefutedList.iff_forall :
    ∀ {l : List DirKey}, AllRefutedList l ↔ ∀ k ∈ l, Refuted (winOf k.1) (boundsOf k.2)
  | [] => by simp [AllRefutedList]
  | k :: ks => by
    simp only [AllRefutedList, List.mem_cons, forall_eq_or_imp]
    exact and_congr Iff.rfl AllRefutedList.iff_forall

theorem AllRefutedList.of_forall {l : List DirKey}
    (h : ∀ k ∈ l, Refuted (winOf k.1) (boundsOf k.2)) : AllRefutedList l :=
  AllRefutedList.iff_forall.2 h

theorem AllRefutedList.append {a b : List DirKey} (ha : AllRefutedList a) (hb : AllRefutedList b) :
    AllRefutedList (a ++ b) :=
  AllRefutedList.of_forall fun k hk => by
    rcases List.mem_append.1 hk with hk | hk
    · exact AllRefutedList.mem ha k hk
    · exact AllRefutedList.mem hb k hk

theorem AllRefutedList.of_subset {l src : List DirKey} (hs : AllRefutedList src)
    (h : ∀ k ∈ l, k ∈ src) : AllRefutedList l :=
  AllRefutedList.of_forall fun k hk => AllRefutedList.mem hs k (h k hk)

/-- Every source list is all-refuted. -/
def AllRefutedSrcs : List (List DirKey) → Prop
  | [] => True
  | s :: ss => AllRefutedList s ∧ AllRefutedSrcs ss

theorem AllRefutedSrcs.mem : ∀ {srcs : List (List DirKey)}, AllRefutedSrcs srcs →
    ∀ s ∈ srcs, AllRefutedList s
  | [], _, s, hs => absurd hs List.not_mem_nil
  | _ :: _, h, s, hs => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact h.1
    · exact AllRefutedSrcs.mem h.2 s hs

/-- The `i`-th entry of a list (`none` past its end). -/
def nthKey : List DirKey → Nat → Option DirKey
  | [], _ => none
  | k :: _, 0 => some k
  | _ :: ks, n + 1 => nthKey ks n

/-- The `j`-th source (empty past the end). -/
def nthSrc : List (List DirKey) → Nat → List DirKey
  | [], _ => []
  | s :: _, 0 => s
  | _ :: ss, n + 1 => nthSrc ss n

theorem nthKey_mem : ∀ {l : List DirKey} {i : Nat} {k : DirKey}, nthKey l i = some k → k ∈ l
  | [], _, _, h => by simp [nthKey] at h
  | k' :: _, 0, k, h => by
    simp only [nthKey, Option.some.injEq] at h
    subst h; exact List.mem_cons_self
  | _ :: ks, i + 1, k, h => List.mem_cons_of_mem _ (nthKey_mem (l := ks) (i := i) h)

theorem nthSrc_mem_or_nil : ∀ (srcs : List (List DirKey)) (j : Nat),
    nthSrc srcs j ∈ srcs ∨ nthSrc srcs j = []
  | [], _ => Or.inr rfl
  | _ :: _, 0 => Or.inl List.mem_cons_self
  | _ :: ss, j + 1 => (nthSrc_mem_or_nil ss j).imp (List.mem_cons_of_mem _) id

/-- One key and its witness `(j, i)`: entry `i` of source `j` is the key. -/
def pickOne (srcs : List (List DirKey)) (k : DirKey) (w : Nat × Nat) : Bool :=
  match nthKey (nthSrc srcs w.1) w.2 with
  | some k' => decide (k' = k)
  | none => false

/-- Every key of the list has a witness in the sources (lists of equal length). -/
def pickOK (srcs : List (List DirKey)) : List DirKey → List (Nat × Nat) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | k :: ks, w :: ws => pickOne srcs k w && pickOK srcs ks ws

theorem pickOne_mem {srcs : List (List DirKey)} {k : DirKey} {w : Nat × Nat}
    (h : pickOne srcs k w = true) : ∃ s ∈ srcs, k ∈ s := by
  unfold pickOne at h
  split at h
  · rename_i k' hk
    have e : k' = k := of_decide_eq_true h
    subst e
    have hm := nthKey_mem hk
    rcases nthSrc_mem_or_nil srcs w.1 with hs | hs
    · exact ⟨_, hs, hm⟩
    · rw [hs] at hm; exact absurd hm List.not_mem_nil
  · exact absurd h Bool.false_ne_true

theorem pickOK_mem : ∀ {srcs : List (List DirKey)} {keys : List DirKey} {ws : List (Nat × Nat)},
    pickOK srcs keys ws = true → ∀ k ∈ keys, ∃ s ∈ srcs, k ∈ s
  | _, [], _, _, k, hk => absurd hk List.not_mem_nil
  | _, _ :: _, [], h, _, _ => by simp [pickOK] at h
  | srcs, k' :: ks, w :: ws, h, k, hk => by
    simp only [pickOK, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hk with rfl | hk
    · exact pickOne_mem h.1
    · exact pickOK_mem h.2 k hk

/-- **The glue.** Keys drawn (by witness) from all-refuted sources are all refuted. -/
theorem allRefuted_of_pick {srcs : List (List DirKey)} {keys : List DirKey} {ws : List (Nat × Nat)}
    (hs : AllRefutedSrcs srcs) (hp : pickOK srcs keys ws = true) : AllRefutedList keys :=
  AllRefutedList.of_forall fun k hk => by
    obtain ⟨s, hs', hks⟩ := pickOK_mem hp k hk
    exact AllRefutedList.mem (AllRefutedSrcs.mem hs s hs') k hks

/-! ### Linear-time witnesses for long key lists

`pickOK` walks a source once per key; with sources of hundreds of keys the kernel caches
too many intermediate terms (more than 2.5 GB for the 1,287 keys of the bound 235).  When the
key list and every source are sorted in the same order (all generators sort keys by
`(length, directions, counts)`), a merge is enough: each key names its source, and that
source is advanced past the key.  Every source is walked once in total. -/

/-- Equality of count or direction lists by `Nat.beq`. -/
def natListEq : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && natListEq as bs
  | _, _ => false

theorem natListEq_eq : ∀ {a b : List Nat}, natListEq a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [natListEq] at h
  | _ :: _, [], h => by simp [natListEq] at h
  | x :: xs, y :: ys, h => by
    simp only [natListEq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, natListEq_eq h.2]

def keyEq (a b : DirKey) : Bool := natListEq a.1 b.1 && natListEq a.2 b.2

theorem keyEq_eq {a b : DirKey} (h : keyEq a b = true) : a = b := by
  simp only [keyEq, Bool.and_eq_true] at h
  exact Prod.ext (natListEq_eq h.1) (natListEq_eq h.2)

/-- Drop entries until the head is `k`; `none` if `k` does not occur. -/
def seek : List DirKey → DirKey → Option (List DirKey)
  | [], _ => none
  | s :: ss, k => if keyEq s k then some (s :: ss) else seek ss k

theorem seek_spec : ∀ {l l' : List DirKey} {k : DirKey}, seek l k = some l' →
    k ∈ l' ∧ ∀ x ∈ l', x ∈ l
  | [], _, _, h => by simp [seek] at h
  | s :: ss, l', k, h => by
    unfold seek at h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨keyEq_eq he ▸ List.mem_cons_self, fun _ hx => hx⟩
    · obtain ⟨h1, h2⟩ := seek_spec h
      exact ⟨h1, fun x hx => List.mem_cons_of_mem _ (h2 x hx)⟩

/-- Replace the `j`-th source. -/
def setSrc : List (List DirKey) → Nat → List DirKey → List (List DirKey)
  | [], _, _ => []
  | _ :: ss, 0, s' => s' :: ss
  | s :: ss, j + 1, s' => s :: setSrc ss j s'

theorem AllRefutedSrcs.nth : ∀ {srcs : List (List DirKey)}, AllRefutedSrcs srcs →
    ∀ j, AllRefutedList (nthSrc srcs j)
  | [], _, _ => trivial
  | _ :: _, h, 0 => h.1
  | _ :: _, h, j + 1 => AllRefutedSrcs.nth h.2 j

theorem AllRefutedSrcs.set : ∀ {srcs : List (List DirKey)}, AllRefutedSrcs srcs →
    ∀ j {s'}, AllRefutedList s' → AllRefutedSrcs (setSrc srcs j s')
  | [], _, _, _, _ => trivial
  | _ :: _, h, 0, _, hs => ⟨hs, h.2⟩
  | _ :: _, h, j + 1, _, hs => ⟨h.1, AllRefutedSrcs.set h.2 j hs⟩

/-- Merge check: key `n` comes from source `ts[n]`, at or after that source's current position. -/
def mergeOK : List (List DirKey) → List DirKey → List Nat → Bool
  | _, [], _ => true
  | _, _ :: _, [] => false
  | srcs, k :: ks, t :: ts =>
    match seek (nthSrc srcs t) k with
    | some s' => mergeOK (setSrc srcs t s') ks ts
    | none => false

theorem allRefuted_of_merge : ∀ {srcs : List (List DirKey)} {keys : List DirKey} {ts : List Nat},
    AllRefutedSrcs srcs → mergeOK srcs keys ts = true → AllRefutedList keys
  | _, [], _, _, _ => trivial
  | _, _ :: _, [], _, h => by simp [mergeOK] at h
  | srcs, k :: ks, t :: ts, hs, h => by
    unfold mergeOK at h
    split at h
    · rename_i s' hk
      obtain ⟨hmem, hsub⟩ := seek_spec hk
      have hs' : AllRefutedList s' :=
        AllRefutedList.of_subset (AllRefutedSrcs.nth hs t) hsub
      exact ⟨AllRefutedList.mem hs' k hmem,
        allRefuted_of_merge (AllRefutedSrcs.set hs t hs') h⟩
    · exact absurd h Bool.false_ne_true

/-- The three-source form used for the bound 235: the 237 keys, the 236 keys and the new
certificates. -/
theorem allRefuted_of_pick3 {a b c : List DirKey} {keys : List DirKey} {ws : List (Nat × Nat)}
    (ha : AllRefutedList a) (hb : AllRefutedList b) (hc : AllRefutedList c)
    (hp : pickOK [a, b, c] keys ws = true) : AllRefutedList keys :=
  allRefuted_of_pick (srcs := [a, b, c])
    (show AllRefutedList a ∧ AllRefutedList b ∧ AllRefutedList c ∧ True from ⟨ha, hb, hc, trivial⟩) hp

/-- The same with merge witnesses. -/
theorem allRefuted_of_merge3 {a b c : List DirKey} {keys : List DirKey} {ts : List Nat}
    (ha : AllRefutedList a) (hb : AllRefutedList b) (hc : AllRefutedList c)
    (hm : mergeOK [a, b, c] keys ts = true) : AllRefutedList keys :=
  allRefuted_of_merge (srcs := [a, b, c])
    (show AllRefutedList a ∧ AllRefutedList b ∧ AllRefutedList c ∧ True from ⟨ha, hb, hc, trivial⟩) hm

end Snake9.LocalWindow
