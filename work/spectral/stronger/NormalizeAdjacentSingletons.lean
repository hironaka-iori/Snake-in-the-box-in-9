import SingletonAlphaBridge

namespace Snake9
open SquareIncidence
noncomputable section
set_option maxHeartbeats 1500000

structure AdjacentSingletonConfig {m : Nat} (p : Snake m) where
  a : Coord
  b : Coord
  c : Coord
  d : Coord
  e : Coord
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  had : a ≠ d
  hbd : b ≠ d
  hcd : c ≠ d
  hae : a ≠ e
  hbe : b ≠ e
  hce : c ≠ e
  ha : InPath p (unit a)
  hb : InPath p (unit b)
  hacsel : InPath p (pair a c)
  cover : ∀ k, InPath p (unit k) → k = a ∨ k = b
  qcover : ∀ k, InPath (translate p (unit a)) (unit k) → k = a ∨ k = c
  forced : ForcedPairsExcept p c d
  qforced : ForcedPairsExcept (translate p (unit a)) b e

theorem forcedPairsExcept_swap {m : Nat} (p : Snake m) (c d : Coord)
    (h : ForcedPairsExcept p c d) : ForcedPairsExcept p d c := by
  intro i j hij hi hj hn
  apply h i j hij hi hj
  tauto

theorem inPath_translate_at {m : Nat} (p : Snake m) (t v : Vertex) :
    InPath (translate p t) v ↔ InPath p (vxor t v) := by
  have h := inPath_translate_iff p t (vxor t v)
  simpa only [vxor_cancel] using h

theorem unit_cover_two {m : Nat} (p : Snake m) (a b : Coord)
    (hz : InPath p 0) (ha : InPath p (unit a)) (hb : InPath p (unit b)) (hab : a ≠ b) :
    ∀ k, InPath p (unit k) → k = a ∨ k = b := by
  intro k hk
  have adj (x : Coord) : Adj 0 (unit x) := (adj_zero_iff _).mpr ⟨x,rfl⟩
  rcases selected_three_neighbors_repeat p hz ha hb hk (adj a) (adj b) (adj k) with h | h | h
  · exact False.elim (hab (unit_injective _ _ h))
  · exact Or.inl (unit_injective _ _ h).symm
  · exact Or.inr (unit_injective _ _ h).symm

theorem config_of_adjacent_internal {m : Nat} (p : Snake m) (i j : Fin (m+1))
    (hi0 : 0 < i.val) (him : i.val < m) (hj0 : 0 < j.val) (hjm : j.val < m)
    (hadj : Adj (p.vertex i) (p.vertex j))
    (halpha : localAlpha p i = 1) (hbeta : localAlpha p j = 1) :
    Nonempty (AdjacentSingletonConfig (translate p (p.vertex i))) := by
  let q := translate p (p.vertex i)
  have hqi : q.vertex i = 0 := vxor_self _
  have hqadj : Adj (q.vertex i) (q.vertex j) := (adj_vxor _ _ _).mpr hadj
  obtain ⟨a, hqa⟩ := (adj_zero_iff (q.vertex j)).mp (hqi ▸ hqadj)
  obtain ⟨k, hki, hjk⟩ := internal_other_neighbor q j i hj0 hjm
  obtain ⟨c, hqac⟩ := neighbor_unit a (hqa ▸ hjk)
  obtain ⟨l, hlj, hil⟩ := internal_other_neighbor q i j hi0 him
  obtain ⟨b, hqb⟩ := (adj_zero_iff (q.vertex l)).mp (hqi ▸ hil)
  have h0 : InPath q 0 := ⟨i,hqi⟩
  have ha : InPath q (unit a) := ⟨j,hqa⟩
  have hb : InPath q (unit b) := ⟨l,hqb⟩
  have hacsel : InPath q (pair a c) := ⟨k,hqac⟩
  have hab : a ≠ b := by
    intro he
    have hv : q.vertex l = q.vertex j := hqb.trans ((congrArg unit he).symm.trans hqa.symm)
    exact hlj (q.distinct l j hv)
  have hac : a ≠ c := by
    intro he
    have hv : q.vertex k = q.vertex i := by rw [hqac, ← he, pair_self, hqi]
    exact hki (q.distinct k i hv)
  have hbc : b ≠ c := by
    intro he
    have hp : InPath q (pair a b) := he ▸ hacsel
    exact selected_no_four_cycle q h0 ha hp hb
      ((adj_zero_iff _).mpr ⟨a,rfl⟩) (unit_pair_adj a b)
      (by rw [pair_comm a b]; exact adj_symmetric (unit_pair_adj b a))
      (adj_symmetric ((adj_zero_iff _).mpr ⟨b,rfl⟩))
      (Ne.symm (pair_nonzero a b hab)) (fun h => hab (unit_injective _ _ h))
  have cover := unit_cover_two q a b h0 ha hb hab
  have halphaq : localAlpha q i = 1 := (localAlpha_translate p _ i).trans halpha
  obtain ⟨r,s,hrs,hr,hs,_,hf⟩ := alpha_one_forced_pairs_zero q i hqi halphaq
  have hcrs : c = r ∨ c = s :=
    arm_coordinate_in_missing q a b r s c hac hbc ha hacsel cover hf
  have hd : ∃ d, c ≠ d ∧ ¬ InPath q (unit c) ∧ ¬ InPath q (unit d) ∧ ForcedPairsExcept q c d := by
    rcases hcrs with he | he
    · subst r
      exact ⟨s,hrs,hr,hs,hf⟩
    · subst s
      exact ⟨r,Ne.symm hrs,hs,hr,forcedPairsExcept_swap q r c hf⟩
  obtain ⟨d,hcd,hcu,hdu,hforced⟩ := hd
  have had : a ≠ d := fun he => hdu (he ▸ ha)
  have hbd : b ≠ d := fun he => hdu (he ▸ hb)
  let z := translate q (unit a)
  have hzj : z.vertex j = 0 := by change vxor (unit a) (q.vertex j) = 0; rw [hqa,vxor_self]
  have hza : InPath z (unit a) := (inPath_translate_at q (unit a) (unit a)).mpr (by simpa [vxor_self] using h0)
  have hzc : InPath z (unit c) := (inPath_translate_at q (unit a) (unit c)).mpr hacsel
  have hz0 : InPath z 0 := ⟨j,hzj⟩
  have qcover := unit_cover_two z a c hz0 hza hzc hac
  have hzab : InPath z (pair a b) := by
    apply (inPath_translate_at q (unit a) (pair a b)).mpr
    simpa only [pair,vxor_cancel] using hb
  have hbetaz : localAlpha z j = 1 := by
    rw [localAlpha_translate,localAlpha_translate]
    exact hbeta
  obtain ⟨r,s,hrs,hr,hs,_,hf⟩ := alpha_one_forced_pairs_zero z j hzj hbetaz
  have hbrs : b = r ∨ b = s :=
    arm_coordinate_in_missing z a c r s b hab (Ne.symm hbc) hza hzab qcover hf
  have he : ∃ e, b ≠ e ∧ ¬ InPath z (unit b) ∧ ¬ InPath z (unit e) ∧ ForcedPairsExcept z b e := by
    rcases hbrs with he | he
    · subst r
      exact ⟨s,hrs,hr,hs,hf⟩
    · subst s
      exact ⟨r,Ne.symm hrs,hs,hr,forcedPairsExcept_swap z r b hf⟩
  obtain ⟨e,hbe,_,heu,hqforced⟩ := he
  have hae : a ≠ e := fun he => heu (he ▸ hza)
  have hce : c ≠ e := fun he => heu (he ▸ hzc)
  exact ⟨⟨a,b,c,d,e,hab,hac,hbc,had,hbd,hcd,hae,hbe,hce,ha,hb,hacsel,cover,qcover,hforced,hqforced⟩⟩

#print axioms config_of_adjacent_internal
end
end Snake9
