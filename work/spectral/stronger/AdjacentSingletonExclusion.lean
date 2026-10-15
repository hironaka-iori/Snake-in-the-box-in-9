import AdjacentNeighborhood
import ExceptionRowNeighbors
import CoordinateCycle

namespace Snake9
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem exists_three_coords_outside_five (a b c d e : Coord) :
    ∃ j : Fin 3 → Coord,
      (∀ k, j k≠a ∧ j k≠b ∧ j k≠c ∧ j k≠d ∧ j k≠e) ∧ Function.Injective j := by
  obtain ⟨f,hf,hfi⟩ := exists_four_coords_outside_five a b c d e
  let cast : Fin 3 → Fin 4 := fun k => ⟨k.val,by omega⟩
  refine ⟨fun k => f (cast k),fun k => hf (cast k),?_⟩
  intro k l he
  have hv := congrArg Fin.val (hfi he)
  exact Fin.ext hv

theorem adjacent_configuration_distinct_false {m : Nat} (p : Snake m)
    (a b c d e : Coord) (h : AdjacentConfig p a b c d e) (hed : e≠d) : False := by
  obtain ⟨j,hj,hji⟩ := exists_three_coords_outside_five a b c d e
  let v : Fin 3 → Fin 2 → Vertex := fun i r =>
    if r=0 then triple a b (j i) else pair e (j i)
  have hv : ∀ i r, InPath p (v i r) := by
    intro i r
    by_cases hr : r=0
    · simp only [v,hr,if_true]
      exact h.selected_abk (j i) (hj i).1 (hj i).2.1 (hj i).2.2.1 (hj i).2.2.2.2
    · simp only [v,hr,if_false]
      apply h.selected_pair e (j i) (Ne.symm (hj i).2.2.2.2)
        (Ne.symm h.hae) (Ne.symm h.hbe) (hj i).1 (hj i).2.1
      simp [Ne.symm h.hce,hed]
  have hd : ∀ i l, i≠l → ∀ r s, v i r ≠ v l s := by
    intro i l hil r s he
    have hli : j l≠j i := fun he => hil (hji he).symm
    have hb := congrArg (fun z : Vertex => z.val.testBit (j i).val) he
    dsimp [v] at hb
    split_ifs at hb <;>
      simp [bit_pair,bit_triple,Ne.symm (hj i).1,Ne.symm (hj i).2.1,
        Ne.symm (hj i).2.2.2.2,hli] at hb
  obtain ⟨i,hi⟩ := exists_good_group p v hv hd
  have ht : ¬ AtMostOneNeighbor p (triple a b (j i)) := by simpa [v] using hi 0
  have he : ¬ AtMostOneNeighbor p (pair e (j i)) := by simpa [v] using hi 1
  have htwo := force_two_neighbors p (triple a b (j i)) (quad a b c (j i))
    (quad a b e (j i)) ht
    (h.triple_neighbor_cover (j i) (hj i).1 (hj i).2.1 (hj i).2.2.1
      (hj i).2.2.2.1 (hj i).2.2.2.2)
  have hmissing := h.selected_abek_excludes_bek (j i) (hj i).1 (hj i).2.1
    (hj i).2.2.1 (hj i).2.2.2.2 htwo.2
  apply he
  exact missing_candidate_low_degree_except p b a c d e (j i)
    (Ne.symm h.hbe) (Ne.symm h.hae) (Ne.symm h.hce) hed
    (hj i).2.1 (hj i).1 (hj i).2.2.1 (hj i).2.2.2.1 (Ne.symm (hj i).2.2.2.2)
    (fun k hk => (h.cover k hk).symm) h.forced hmissing

theorem adjacent_configuration_equal_false {m : Nat} (p : Snake m)
    (a b c d : Coord) (h : AdjacentConfig p a b c d d) : False := by
  obtain ⟨j,hj,hji⟩ := exists_three_coords_outside_five a b c d d
  let v : Fin 3 → Fin 3 → Vertex := fun i r =>
    if r=0 then triple a b (j i) else if r=1 then pair c (j i) else pair d (j i)
  have hv : ∀ i r, InPath p (v i r) := by
    intro i r
    by_cases hr : r=0
    · simp only [v,hr,if_true]
      exact h.selected_abk (j i) (hj i).1 (hj i).2.1 (hj i).2.2.1 (hj i).2.2.2.1
    · simp only [v,hr,if_false]
      by_cases hr1 : r=1
      · rw [if_pos hr1]
        apply h.selected_pair c (j i) (Ne.symm (hj i).2.2.1)
          (Ne.symm h.hac) (Ne.symm h.hbc) (hj i).1 (hj i).2.1
        simp [h.hcd,(hj i).2.2.2.1]
      · rw [if_neg hr1]
        apply h.selected_pair d (j i) (Ne.symm (hj i).2.2.2.1)
          (Ne.symm h.had) (Ne.symm h.hbd) (hj i).1 (hj i).2.1
        simp [Ne.symm h.hcd,(hj i).2.2.1]
  have hd : ∀ i l, i≠l → ∀ r s, v i r ≠ v l s := by
    intro i l hil r s he
    have hli : j l≠j i := fun he => hil (hji he).symm
    have hb := congrArg (fun z : Vertex => z.val.testBit (j i).val) he
    dsimp [v] at hb
    split_ifs at hb <;>
      simp [bit_pair,bit_triple,Ne.symm (hj i).1,Ne.symm (hj i).2.1,
        Ne.symm (hj i).2.2.1,Ne.symm (hj i).2.2.2.1,hli] at hb
  obtain ⟨i,hi⟩ := exists_good_group p v hv hd
  have ht : ¬ AtMostOneNeighbor p (triple a b (j i)) := by simpa [v] using hi 0
  have hc : ¬ AtMostOneNeighbor p (pair c (j i)) := by simpa [v] using hi 1
  have hd : ¬ AtMostOneNeighbor p (pair d (j i)) := by simpa [v] using hi 2
  have htwo := force_two_neighbors p (triple a b (j i)) (quad a b c (j i))
    (quad a b d (j i)) ht
    (h.triple_neighbor_cover (j i) (hj i).1 (hj i).2.1 (hj i).2.2.1
      (hj i).2.2.2.1 (hj i).2.2.2.1)
  have hmissing := h.selected_abek_excludes_bek (j i) (hj i).1 (hj i).2.1
    (hj i).2.2.1 (hj i).2.2.2.1 htwo.2
  have hdtwo := force_two_neighbors p (pair d (j i)) (triple a d (j i))
    (triple c d (j i)) hd
    (h.row_d_neighbors (j i) (hj i).1 (hj i).2.1 (hj i).2.2.1 (hj i).2.2.2.1 hmissing)
  have hctwo := force_two_neighbors p (pair c (j i)) (triple b c (j i))
    (triple c d (j i)) hc
    (h.row_c_neighbors (j i) (hj i).1 (hj i).2.1 (hj i).2.2.1 (hj i).2.2.2.1)
  apply selected_coordinate_cycle8_false p a b c d (j i)
    h.hab h.hac h.had (Ne.symm (hj i).1) h.hbc h.hbd (Ne.symm (hj i).2.1)
    h.hcd (Ne.symm (hj i).2.2.1) (Ne.symm (hj i).2.2.2.1)
  · exact h.selected_abk (j i) (hj i).1 (hj i).2.1 (hj i).2.2.1 (hj i).2.2.2.1
  · exact htwo.1
  · exact hctwo.1
  · simpa [v] using hv i 1
  · exact hdtwo.2
  · simpa [v] using hv i 2
  · exact hdtwo.1
  · exact htwo.2

theorem adjacent_configuration_impossible {m : Nat} (p : Snake m)
    (a b c d e : Coord) (h : AdjacentConfig p a b c d e) : False := by
  by_cases hed : e=d
  · subst e
    exact adjacent_configuration_equal_false p a b c d h
  · exact adjacent_configuration_distinct_false p a b c d e h hed

#print axioms adjacent_configuration_distinct_false
#print axioms adjacent_configuration_equal_false
#print axioms adjacent_configuration_impossible
end Snake9
