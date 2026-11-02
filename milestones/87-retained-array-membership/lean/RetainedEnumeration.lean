import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace Snake9.Enumeration87

/-- The full edge identity is (direction, history, six-count code). -/
abbrev Row := Nat × Nat × Nat

def acceptedCodes (keep : Nat → Nat → Nat → Bool) (d q : Nat) : List Nat :=
  (List.range 46656).filter (keep d q)

def generatedRows (keep : Nat → Nat → Nat → Bool) : List Row :=
  (List.range 505).flatMap fun d =>
    (List.range 75).flatMap fun q =>
      (acceptedCodes keep d q).map fun c => (d,q,c)

theorem accepted_code_iff (keep : Nat → Nat → Nat → Bool) (d q c : Nat) :
    c ∈ acceptedCodes keep d q ↔ c < 46656 ∧ keep d q c = true := by
  simp [acceptedCodes]

theorem generated_row_iff (keep : Nat → Nat → Nat → Bool) (d q c : Nat) :
    (d,q,c) ∈ generatedRows keep ↔
      d < 505 ∧ q < 75 ∧ c < 46656 ∧ keep d q c = true := by
  simp [generatedRows, List.mem_flatMap, accepted_code_iff]

/-- One-sided coverage suffices for transferring an actual path to a saved graph. -/
def RetentionCover (keep : Nat → Nat → Nat → Bool) (rows : List Row) : Prop :=
  ∀ d q c, d < 505 → q < 75 → c < 46656 → keep d q c = true →
    (d,q,c) ∈ rows

theorem retention_cover_iff_subset (keep : Nat → Nat → Nat → Bool) (rows : List Row) :
    RetentionCover keep rows ↔ generatedRows keep ⊆ rows := by
  constructor
  · intro h key hk
    obtain ⟨d,q,c⟩ := key
    obtain ⟨hd,hq,hc,hkeep⟩ := (generated_row_iff keep d q c).mp hk
    exact h d q c hd hq hc hkeep
  · intro h d q c hd hq hc hkeep
    exact h ((generated_row_iff keep d q c).mpr ⟨hd,hq,hc,hkeep⟩)

theorem exact_generator_covers (keep : Nat → Nat → Nat → Bool) (rows : List Row)
    (heq : rows = generatedRows keep) : RetentionCover keep rows := by
  rw [retention_cover_iff_subset, heq]
  exact fun _ h => h

theorem covering_row_index (keep : Nat → Nat → Nat → Bool) (rows : Array Row)
    (hcover : RetentionCover keep rows.toList) (d q c : Nat)
    (hd : d < 505) (hq : q < 75) (hc : c < 46656) (hk : keep d q c = true) :
    ∃ i : Nat, rows.toList[i]? = some (d,q,c) :=
  List.getElem?_of_mem (hcover d q c hd hq hc hk)

/-- Adding rows preserves coverage; their weights still require separate checks. -/
theorem retention_cover_mono (keep : Nat → Nat → Nat → Bool) (rows more : List Row)
    (hcover : RetentionCover keep rows) (hsub : rows ⊆ more) :
    RetentionCover keep more := by
  intro d q c hd hq hc hk
  exact hsub (hcover d q c hd hq hc hk)

/-- The equality premise is a finite-data obligation, not a catalogue theorem. -/
theorem saved_row_index (keep : Nat → Nat → Nat → Bool) (rows : Array Row)
    (heq : rows.toList = generatedRows keep) (d q c : Nat)
    (hd : d < 505) (hq : q < 75) (hc : c < 46656) (hk : keep d q c = true) :
    ∃ i : Nat, rows.toList[i]? = some (d,q,c) := by
  apply List.getElem?_of_mem
  rw [heq, generated_row_iff]
  exact ⟨hd,hq,hc,hk⟩

/-- Index the selected code inside a block, then add the preceding row count. -/
theorem prefix_rank_index {α : Type*} [DecidableEq α]
    (before block after : List α) (x : α) (hx : x ∈ block) :
    (before ++ block ++ after)[before.length + block.idxOf x]? = some x := by
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (List.idxOf_lt_length hx)]
  exact List.getElem?_idxOf hx

theorem flattened_block_index {α : Type*} [DecidableEq α]
    (before after : List (List α)) (block : List α) (x : α) (hx : x ∈ block) :
    (before ++ block :: after).flatten[before.flatten.length + block.idxOf x]? =
      some x := by
  simpa only [List.flatten_append, List.flatten_cons, List.append_assoc] using
    prefix_rank_index before.flatten block after.flatten x hx

/-- A full-key index is unique when the recorded key list has no duplicates. -/
theorem full_key_index_unique (rows : List Row) (hn : rows.Nodup)
    (i j : Nat) (hi : i < rows.length) (hj : j < rows.length)
    (he : rows[i] = rows[j]) : i = j :=
  hn.getElem_inj_iff.mp he

/-- Row-indexed endpoints require no uniqueness assumption about endpoint pairs. -/
theorem indexed_endpoint_maps (rows : List Row) (source target : Row → Nat)
    (i : Nat) (key : Row) (hi : rows[i]? = some key) :
    (rows.map source)[i]? = some (source key) ∧
    (rows.map target)[i]? = some (target key) := by
  simp [hi]

#print axioms accepted_code_iff
#print axioms generated_row_iff
#print axioms retention_cover_iff_subset
#print axioms exact_generator_covers
#print axioms covering_row_index
#print axioms retention_cover_mono
#print axioms saved_row_index
#print axioms prefix_rank_index
#print axioms flattened_block_index
#print axioms full_key_index_unique
#print axioms indexed_endpoint_maps
end Snake9.Enumeration87
