import EightEdges171

namespace Snake9.Count171

theorem missing_count_eq_graph_edges {m : Nat} (p : Snake m) :
    missingPairCount p = Nat.card (missingGraph p).edgeSet := by
  classical
  let L := axes.filter (fun ab => decide (Component170.MissingEdge p ab.1 ab.2))
  let S := L.toFinset
  let f : Coord × Coord → Sym2 Coord := fun ab => s(ab.1,ab.2)
  have memS (ab : Coord × Coord) : ab ∈ S ↔
      ab.1.val < ab.2.val ∧ Component170.MissingEdge p ab.1 ab.2 := by
    simp only [S,L,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,mem_axes]
  have heq : (missingGraph p).edgeFinset = S.image f := by
    apply Finset.ext
    intro e
    refine Sym2.ind ?_ e
    intro a b
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change Component170.MissingEdge p a b ↔ s(a,b) ∈ S.image f
    constructor
    · intro hab
      by_cases hlt : a.val < b.val
      · exact Finset.mem_image.mpr ⟨(a,b),(memS (a,b)).mpr ⟨hlt,hab⟩,rfl⟩
      · have hne : a.val ≠ b.val := fun he => hab.1 (Fin.ext he)
        have hgt : b.val < a.val := by omega
        refine Finset.mem_image.mpr ⟨(b,a),(memS (b,a)).mpr
          ⟨hgt,Component170.missing_edge_symm p hab⟩,?_⟩
        exact Sym2.eq_swap
    · intro he
      obtain ⟨ab,hab,he⟩ := Finset.mem_image.mp he
      have hE := ((memS ab).mp hab).2
      change s(ab.1,ab.2) = s(a,b) at he
      rcases Sym2.eq_iff.mp he with hh | hh
      · simpa only [hh.1,hh.2] using hE
      · have hrev := Component170.missing_edge_symm p hE
        simpa only [hh.1,hh.2] using hrev
  have hinj : Set.InjOn f (↑S : Set (Coord × Coord)) := by
    intro ab hab cd hcd he
    have hlt1 := ((memS ab).mp hab).1
    have hlt2 := ((memS cd).mp hcd).1
    change s(ab.1,ab.2) = s(cd.1,cd.2) at he
    rcases Sym2.eq_iff.mp he with hh | hh
    · exact Prod.ext hh.1 hh.2
    · have hv1 := congrArg Fin.val hh.1
      have hv2 := congrArg Fin.val hh.2
      omega
  have hn : L.Nodup := axes_nodup.filter _
  have hcard : (S.image f).card = S.card := Finset.card_image_iff.mpr hinj
  calc
    missingPairCount p = L.length := by
      exact List.countP_eq_length_filter
    _ = S.card := (List.toFinset_card_of_nodup hn).symm
    _ = (S.image f).card := hcard.symm
    _ = (missingGraph p).edgeFinset.card := congrArg Finset.card heq.symm
    _ = Nat.card (missingGraph p).edgeSet := by
      rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]

theorem undominated_eight_empty_squares {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (q : Vertex) (hq : ∀ v, InPath p v → ¬ Adj q v) :
    8 ≤ emptySquareCount p q := by
  rw [empty_count_eq_missing_count p hm q hq, missing_count_eq_graph_edges]
  exact missing_graph_eight_edges (translate p q) (Component170.translated_units_absent p q hq)

#print axioms missing_count_eq_graph_edges
#print axioms undominated_eight_empty_squares
end Snake9.Count171
