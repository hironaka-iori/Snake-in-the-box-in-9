import ExactHistory

/-! Numeric dictionary indices and complete signature recognition.
No direction table or finite graph is imported. -/
namespace Snake9.History77
open Snake9.History75

variable {α : Type} [DecidableEq α]

/-- A signature needs its proper prefix in the dictionary; the signature
itself need not be a dictionary entry. -/
theorem signature_suffix_iff {D : List (List α)} {w s t : List α}
    (hs : IsLongest D w s) (a : α) (hprefix : t.dropLast ∈ D) :
    t <:+ w ++ [a] ↔ t <:+ s ++ [a] := by
  constructor
  · intro htw
    by_cases hn : t = []
    · simp [hn]
    · have hdrop : t.dropLast <:+ w := by
        obtain ⟨u, hu⟩ := htw
        refine ⟨u, ?_⟩
        have h := congrArg List.dropLast hu
        simpa [List.dropLast_append_of_ne_nil hn] using h
      have hsuf : t.dropLast <:+ s :=
        List.suffix_of_suffix_length_le hdrop hs.2.1
          (hs.2.2 _ hprefix hdrop)
      have hlast : t.getLast hn = a := by
        have h := htw.getLast hn
        simpa using h
      rw [← List.dropLast_concat_getLast hn, hlast]
      exact suffix_append_one hsuf a
  · intro hts
    exact hts.trans (suffix_append_one hs.2.1 a)

theorem dictionary_index_decode {D : List (List α)} {s : List α}
    (hs : s ∈ D) (fallback : List α) :
    D.getD (D.idxOf s) fallback = s := by
  induction D with
  | nil => simp at hs
  | cons a D ih =>
    by_cases h : s = a
    · subst s
      simp
    · have hm : s ∈ D := by simpa [h] using hs
      have hb : (a == s) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
      rw [List.idxOf_cons, hb]
      simpa using ih hm

def historyIndex (w : List Nat) : Nat :=
  prefixes.idxOf (run prefixes w)

theorem history_index_lt (w : List Nat) : historyIndex w < 75 := by
  have h := List.idxOf_lt_length (exact_history_invariant w).1
  simpa only [historyIndex, prefixes_length] using h

theorem history_decode (w : List Nat) (fallback : List Nat) :
    prefixes.getD (historyIndex w) fallback = run prefixes w :=
  dictionary_index_decode (exact_history_invariant w).1 fallback

theorem history_index_empty : historyIndex [] = 0 := by rfl

theorem stored_append_last (w : List Nat) (a : Nat)
    (hn : run prefixes (w ++ [a]) ≠ []) :
    (run prefixes (w ++ [a])).getLast hn = a := by
  have h := (exact_history_invariant (w ++ [a])).2.1.getLast hn
  simpa using h

theorem decoded_append_last (w : List Nat) (a : Nat)
    (hn : prefixes.getD (historyIndex (w ++ [a])) [] ≠ []) :
    (prefixes.getD (historyIndex (w ++ [a])) []).getLast hn = a := by
  simpa only [history_decode] using stored_append_last w a
    (by simpa only [history_decode] using hn)

theorem exact_signature_iff (w : List Nat) (a : Nat) (sig : List Nat)
    (hsig : sig ∈ signatures) :
    sig <:+ w ++ [a] ↔ sig <:+ run prefixes w ++ [a] :=
  signature_suffix_iff (exact_history_invariant w) a
    (signatures_valid sig hsig).2

theorem indexed_signature_iff (w : List Nat) (a : Nat) (sig : List Nat)
    (hsig : sig ∈ signatures) :
    sig <:+ w ++ [a] ↔
      sig <:+ prefixes.getD (historyIndex w) [] ++ [a] := by
  simpa only [history_decode] using exact_signature_iff w a sig hsig

#print axioms signature_suffix_iff
#print axioms dictionary_index_decode
#print axioms history_index_lt
#print axioms history_decode
#print axioms history_index_empty
#print axioms stored_append_last
#print axioms decoded_append_last
#print axioms exact_signature_iff
#print axioms indexed_signature_iff
end Snake9.History77
