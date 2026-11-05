import GraphCount171

namespace Snake9.Count171

theorem five_clique_edge_bound {m : Nat} (p : Snake m) (P : Coord → Prop)
    [Fintype {x // P x}] (hsize : 5 ≤ Fintype.card {x // P x})
    (hc : ∀ a b, P a → P b → a ≠ b → ¬ InPath p (pair a b)) :
    10 ≤ Nat.card (missingGraph p).edgeSet := by
  classical
  let f : (⊤ : SimpleGraph {x // P x}) ↪g missingGraph p :=
    { toFun := Subtype.val
      inj' := Subtype.val_injective
      map_rel_iff' := by
        intro u v
        change Component170.MissingEdge p u.val v.val ↔ u ≠ v
        constructor
        · intro he huv
          exact he.1 (congrArg Subtype.val huv)
        · intro hne
          have hvals : u.val ≠ v.val := fun he => hne (Subtype.ext he)
          exact ⟨hvals, hc u.val v.val u.property v.property hvals⟩ }
  have hcard := Nat.card_le_card_of_injective f.mapEdgeSet f.mapEdgeSet.injective
  have ht : Nat.card (⊤ : SimpleGraph {x // P x}).edgeSet =
      (Fintype.card {x // P x}).choose 2 := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  rw [ht] at hcard
  have hn : 10 ≤ (Fintype.card {x // P x}).choose 2 := Nat.choose_le_choose 2 hsize
  omega

theorem missing_graph_eight_edges {m : Nat} (p : Snake m)
    (h0 : ∀ k : Coord, ¬ InPath p (unit k)) :
    8 ≤ Nat.card (missingGraph p).edgeSet := by
  classical
  by_cases hconn : ∀ a b, Component170.MissingReach p a b
  · exact connected_missing_graph_edge_bound p hconn
  · have hex : ∃ a b, ¬ Component170.MissingReach p a b := by
      by_contra hn
      apply hconn
      intro a b
      by_contra hab
      exact hn ⟨a,b,hab⟩
    obtain ⟨root,outside,hout⟩ := hex
    let P : Coord → Prop := Component170.MissingReach p root
    have hcard : Fintype.card {x // ¬ P x} = 9 - Fintype.card {x // P x} := by
      simpa [Coord] using Fintype.card_subtype_compl P
    by_cases hsize : 5 ≤ Fintype.card {x // P x}
    · have hten := five_clique_edge_bound p P hsize
        (Component170.missing_component_complete p h0 root outside hout)
      omega
    · have hsize' : 5 ≤ Fintype.card {x // ¬ P x} := by omega
      have hten := five_clique_edge_bound p (fun x => ¬ P x) hsize'
        (Component170.missing_complement_complete p h0 root outside hout)
      omega

#print axioms five_clique_edge_bound
#print axioms missing_graph_eight_edges
end Snake9.Count171
