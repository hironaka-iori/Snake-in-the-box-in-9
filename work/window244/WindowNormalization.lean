import WindowPermutation
import CoordinateExtension
import NormalizeThreeCenters

namespace Snake9.Window244
open SquareIncidence
noncomputable section
set_option maxHeartbeats 800000

theorem permute_pair (σ : Equiv.Perm Coord) (a b : Coord) :
    permuteVertex σ (pair a b) = pair (σ a) (σ b) := by
  change permuteVertex σ (flip b (unit a)) = flip (σ b) (unit (σ a))
  rw [permute_flip,permute_unit]

theorem permute_triple (σ : Equiv.Perm Coord) (a b c : Coord) :
    permuteVertex σ (triple a b c) = triple (σ a) (σ b) (σ c) := by
  change permuteVertex σ (flip c (pair a b)) = flip (σ c) (pair (σ a) (σ b))
  rw [permute_flip,permute_pair]

def standardize {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) : Snake m :=
  translate (permuteSnake σ p) (unit 0)

theorem alpha_standardize {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m)
    (i : Fin (m+1)) : localAlpha (standardize σ p) i = localAlpha p i := by
  exact (localAlpha_translate (permuteSnake σ p) (unit 0) i).trans (localAlpha_permute σ p i)

theorem selected_standardize {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m)
    (v : Vertex) (hv : InPath p v) :
    InPath (standardize σ p) (vxor (unit 0) (permuteVertex σ v)) :=
  (inPath_translate_iff (permuteSnake σ p) (unit 0) _).mpr ((inPath_permute_iff σ p v).mpr hv)

theorem standardize_config {m : Nat} (p : Snake m) (i j k : Fin (m+1))
    (h : NormalizedThreeCenters p i j k) (σ : Equiv.Perm Coord) (e : Coord)
    (hc : σ h.c = 0) (ha : σ h.a = 1) (hb : σ h.b = 2) (hd : σ h.d = e) :
    (standardize σ p).vertex i = 1 ∧ (standardize σ p).vertex j = 3 ∧
    (standardize σ p).vertex k = 7 ∧ InPath (standardize σ p) 0 ∧
    InPath (standardize σ p) (vxor (unit 0) (triple 1 2 e)) := by
  have hz := selected_standardize σ p _ h.before_selected
  rw [permute_unit,hc,vxor_self] at hz
  have hl := selected_standardize σ p _ h.after_selected
  rw [permute_triple,ha,hb,hd] at hl
  refine ⟨?_,?_,?_,hz,hl⟩
  · change vxor (unit 0) (permuteVertex σ (p.vertex i)) = 1
    rw [h.left_eq,permute_zero]
    decide
  · change vxor (unit 0) (permuteVertex σ (p.vertex j)) = 3
    rw [h.middle_eq,permute_unit,ha]
    decide
  · change vxor (unit 0) (permuteVertex σ (p.vertex k)) = 7
    rw [h.right_eq,permute_pair,ha,hb]
    decide

/-- Both possible five-vertex shapes are covered, without an alpha premise.
All alpha values, at every path index, are preserved. -/
theorem normalize_five_to_standard {m : Nat} (p : Snake m) (r : Nat) (hr : r+4 ≤ m) :
    ∃ q : Snake m, (∀ i, localAlpha q i = localAlpha p i) ∧
      q.vertex ⟨r+1,by omega⟩ = 1 ∧ q.vertex ⟨r+2,by omega⟩ = 3 ∧
      q.vertex ⟨r+3,by omega⟩ = 7 ∧
      ((∀ v ∈ ([0,1,3,7,6] : List Vertex), InPath q v) ∨
       (∀ v ∈ ([0,1,3,7,15] : List Vertex), InPath q v)) := by
  obtain ⟨h⟩ := normalize_five_vertex_window p r hr
  let p0 := translate p (p.vertex ⟨r+1,by omega⟩)
  by_cases hcd : h.c = h.d
  · obtain ⟨σ,hc,ha,hb⟩ := coordinate_permutation_three h.c h.a h.b h.hac h.hbc h.hab
    have hd : σ h.d = 0 := by rw [←hcd]; exact hc
    have hs := standardize_config p0 _ _ _ h σ 0 hc ha hb hd
    let q := standardize σ p0
    refine ⟨q,?_,hs.1,hs.2.1,hs.2.2.1,Or.inl ?_⟩
    · intro i
      exact (alpha_standardize σ p0 i).trans (localAlpha_translate p _ i)
    · intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact hs.2.2.2.1
      · exact ⟨_,hs.1⟩
      · exact ⟨_,hs.2.1⟩
      · exact ⟨_,hs.2.2.1⟩
      · exact hs.2.2.2.2
  · obtain ⟨σ,hc,ha,hb,hd⟩ := coordinate_permutation_four h.c h.a h.b h.d h.hac h.hbc h.hab h.hda h.hdb hcd
    have hs := standardize_config p0 _ _ _ h σ 3 hc ha hb hd
    let q := standardize σ p0
    refine ⟨q,?_,hs.1,hs.2.1,hs.2.2.1,Or.inr ?_⟩
    · intro i
      exact (alpha_standardize σ p0 i).trans (localAlpha_translate p _ i)
    · intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact hs.2.2.2.1
      · exact ⟨_,hs.1⟩
      · exact ⟨_,hs.2.1⟩
      · exact ⟨_,hs.2.2.1⟩
      · exact hs.2.2.2.2

#print axioms alpha_standardize
#print axioms standardize_config
#print axioms normalize_five_to_standard
end
end Snake9.Window244
