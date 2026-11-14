import Capacity209

/-!
Source prepared for checking; not compiled by its author.
The hypotheses concern distinct assigned words in two lists. Geometry
and the interpretation of native domain operations remain separate.
-/

namespace Spare211

/-- Words used outside C but absent from C consume the spare capacity.
The two lists need not be disjoint; only the filtered outside list is. -/
theorem spare_capacity (C O pool : List Nat)
    (hC : C.Nodup) (hO : O.Nodup)
    (hCpool : ∀ w, w ∈ C → w ∈ pool)
    (hOpool : ∀ w, w ∈ O → w ∈ pool) :
    C.length + (O.filter (fun w => !(C.contains w))).length ≤ pool.length := by
  have hdistinct : (C ++ O.filter (fun w => !(C.contains w))).Nodup := by
    apply List.pairwise_append.mpr
    refine ⟨hC, List.Pairwise.filter (fun w => !(C.contains w)) hO, ?_⟩
    intro a ha b hb heq
    have hbnot : b ∉ C := by
      simpa using (List.mem_filter.mp hb).2
    exact hbnot (heq ▸ ha)
  have hsubset :
      ∀ w, w ∈ C ++ O.filter (fun w => !(C.contains w)) → w ∈ pool := by
    intro w hw
    rcases List.mem_append.mp hw with hc | ho
    · exact hCpool w hc
    · exact hOpool w (List.mem_filter.mp ho).1
  have hbound :=
    Capacity209.distinct_length_le
      (C ++ O.filter (fun w => !(C.contains w))) pool hdistinct hsubset
  simpa using hbound

/-- A family using 31 distinct words leaves at most one outside word
absent from the family when the alphabet has size 32. -/
theorem one_spare_word (C O pool : List Nat)
    (hbound :
      C.length + (O.filter (fun w => !(C.contains w))).length ≤ pool.length)
    (hC : C.length = 31) (hpool : pool.length = 32) :
    (O.filter (fun w => !(C.contains w))).length ≤ 1 := by
  omega

/-- The corresponding consequence for a 30-word family. -/
theorem two_spare_words (C O pool : List Nat)
    (hbound :
      C.length + (O.filter (fun w => !(C.contains w))).length ≤ pool.length)
    (hC : C.length = 30) (hpool : pool.length = 32) :
    (O.filter (fun w => !(C.contains w))).length ≤ 2 := by
  omega

#print axioms spare_capacity
#print axioms one_spare_word
#print axioms two_spare_words

end Spare211
