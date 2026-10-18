import CubeLocal
import Mathlib.Tactic
import Mathlib.Data.Finset.SymmDiff

namespace Snake9.FaceRepair
open Finset Classical
open scoped symmDiff

def varying (s : Finset Vertex) : Finset Coord :=
  univ.filter (fun k => ∃ v ∈ s, ∃ w ∈ s, v.val.testBit k.val ≠ w.val.testBit k.val)

def face (a : Vertex) (free : Finset Coord) : Finset Vertex :=
  univ.filter (fun v => ∀ k, k ∉ free → v.val.testBit k.val = a.val.testBit k.val)

theorem outside_agreement_iff (s t region : Finset Vertex) :
    (∀ v, v ∉ region → (v ∈ s ↔ v ∈ t)) ↔ s ∆ t ⊆ region := by
  constructor
  · intro h v hv
    by_contra hn
    have he := h v hn
    simp only [mem_symmDiff] at hv
    rcases hv with ⟨hs,ht⟩ | ⟨ht,hs⟩
    · exact ht (he.mp hs)
    · exact hs (he.mpr ht)
  · intro h v hn
    constructor
    · intro hs
      by_contra ht
      exact hn (h (mem_symmDiff.mpr (Or.inl ⟨hs,ht⟩)))
    · intro ht
      by_contra hs
      exact hn (h (mem_symmDiff.mpr (Or.inr ⟨ht,hs⟩)))

theorem varying_subset_of_face (s : Finset Vertex) (a : Vertex) (free : Finset Coord)
    (h : s ⊆ face a free) : varying s ⊆ free := by
  intro k hk
  obtain ⟨_,v,hv,w,hw,hne⟩ := mem_filter.mp hk
  by_contra hn
  have hv' := (mem_filter.mp (h hv)).2 k hn
  have hw' := (mem_filter.mp (h hw)).2 k hn
  exact hne (hv'.trans hw'.symm)

theorem subset_face_varying (s : Finset Vertex) {a : Vertex} (ha : a ∈ s) :
    s ⊆ face a (varying s) := by
  intro v hv
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  intro k hk
  by_contra hn
  exact hk (mem_filter.mpr ⟨mem_univ _,v,hv,a,ha,hn⟩)

theorem face_mono (a : Vertex) {s t : Finset Coord} (hst : s ⊆ t) :
    face a s ⊆ face a t := by
  intro v hv
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  intro k hk
  exact (mem_filter.mp hv).2 k (fun hs => hk (hst hs))

theorem contained_six_face_iff (s : Finset Vertex) (hne : s.Nonempty) :
    (∃ a free, free.card = 6 ∧ s ⊆ face a free) ↔ (varying s).card ≤ 6 := by
  constructor
  · rintro ⟨a,free,hcard,hsub⟩
    have h := card_le_card (varying_subset_of_face s a free hsub)
    omega
  · intro hc
    obtain ⟨a,ha⟩ := hne
    obtain ⟨free,hvf,hfu,hcard⟩ :=
      exists_subsuperset_card_eq (subset_univ (varying s)) hc
        (show 6 ≤ (univ : Finset Coord).card by decide)
    exact ⟨a,free,hcard,(subset_face_varying s ha).trans (face_mono a hvf)⟩

theorem repair_six_face_iff (s t : Finset Vertex) (hne : (s ∆ t).Nonempty) :
    (∃ a free, free.card = 6 ∧ ∀ v, v ∉ face a free → (v ∈ s ↔ v ∈ t)) ↔
      (varying (s ∆ t)).card ≤ 6 := by
  simpa only [outside_agreement_iff] using contained_six_face_iff (s ∆ t) hne

theorem six_face_count_arithmetic : Nat.choose 9 6 * 2^(9-6) = 672 := by decide
theorem seven_face_count_arithmetic : Nat.choose 9 7 * 2^(9-7) = 144 := by decide

#print axioms outside_agreement_iff
#print axioms varying_subset_of_face
#print axioms subset_face_varying
#print axioms face_mono
#print axioms contained_six_face_iff
#print axioms repair_six_face_iff
#print axioms six_face_count_arithmetic
#print axioms seven_face_count_arithmetic
end Snake9.FaceRepair
