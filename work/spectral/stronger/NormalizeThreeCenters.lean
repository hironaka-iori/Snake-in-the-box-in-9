import RepeatedThreeTwosExclusion

namespace Snake9
open SquareIncidence
noncomputable section
set_option maxHeartbeats 1500000

structure NormalizedThreeCenters {m : Nat} (p : Snake m) (i j k : Fin (m+1)) where
  a : Coord
  b : Coord
  c : Coord
  d : Coord
  hab : a≠b
  hac : a≠c
  hbc : b≠c
  hda : d≠a
  hdb : d≠b
  left_eq : p.vertex i=0
  middle_eq : p.vertex j=unit a
  right_eq : p.vertex k=pair a b
  before_selected : InPath p (unit c)
  after_selected : InPath p (triple a b d)

theorem normalize_five_vertex_window {m : Nat} (p : Snake m) (r : Nat) (hr : r+4≤m) :
    Nonempty (NormalizedThreeCenters
      (translate p (p.vertex ⟨r+1,by omega⟩))
      ⟨r+1,by omega⟩ ⟨r+2,by omega⟩ ⟨r+3,by omega⟩) := by
  let q := translate p (p.vertex ⟨r+1,by omega⟩)
  let t : Fin (m+1) := ⟨r,by omega⟩
  let i : Fin (m+1) := ⟨r+1,by omega⟩
  let j : Fin (m+1) := ⟨r+2,by omega⟩
  let k : Fin (m+1) := ⟨r+3,by omega⟩
  let l : Fin (m+1) := ⟨r+4,by omega⟩
  have hi : q.vertex i=0 := vxor_self _
  have hit : Adj (q.vertex i) (q.vertex t) := (path_adj_iff q i t).mpr (Or.inr (by dsimp [i,t]))
  have hij : Adj (q.vertex i) (q.vertex j) := (path_adj_iff q i j).mpr (Or.inl (by dsimp [i,j]))
  have hjk : Adj (q.vertex j) (q.vertex k) := (path_adj_iff q j k).mpr (Or.inl (by dsimp [j,k]))
  have hkl : Adj (q.vertex k) (q.vertex l) := (path_adj_iff q k l).mpr (Or.inl (by dsimp [k,l]))
  obtain ⟨a,ha⟩ := (adj_zero_iff _).mp (hi ▸ hij)
  obtain ⟨c,hc⟩ := (adj_zero_iff _).mp (hi ▸ hit)
  obtain ⟨b,hb⟩ := neighbor_unit a (ha ▸ hjk)
  obtain ⟨d,hd⟩ := neighbor_pair a b (hb ▸ hkl)
  have hab : a≠b := by
    intro he
    have hv : q.vertex k=q.vertex i := by rw [hb,←he,pair_self,hi]
    have hki := congrArg Fin.val (q.distinct k i hv)
    dsimp [k,i] at hki
    omega
  have hac : a≠c := by
    intro he
    have hv : q.vertex j=q.vertex t := ha.trans ((congrArg unit he).trans hc.symm)
    have hjt := congrArg Fin.val (q.distinct j t hv)
    dsimp [j,t] at hjt
    omega
  have hbc : b≠c := by
    intro he
    have htk : Adj (q.vertex t) (q.vertex k) := by
      rw [hc,hb,←he,pair_comm]
      exact unit_pair_adj b a
    have htki := (path_adj_iff q t k).mp htk
    dsimp [t,k] at htki
    omega
  have hdb : d≠b := by
    intro he
    have hv : q.vertex l=q.vertex j := by rw [hd,he,triple_cancel_right,ha]
    have hlj := congrArg Fin.val (q.distinct l j hv)
    dsimp [l,j] at hlj
    omega
  have hda : d≠a := by
    intro he
    have hil : Adj (q.vertex i) (q.vertex l) := by
      rw [hi,hd,he,triple_cancel_left]
      exact (adj_zero_iff _).mpr ⟨b,rfl⟩
    have hili := (path_adj_iff q i l).mp hil
    dsimp [i,l] at hili
    omega
  exact ⟨⟨a,b,c,d,hab,hac,hbc,hda,hdb,hi,ha,hb,⟨t,hc⟩,⟨l,hd⟩⟩⟩

/-- Once the repeated-coordinate case is excluded, any three consecutive
internal count-two vertices normalize to four distinct transition coordinates. -/
theorem normalize_three_twos_to_distinct_window {m : Nat} (p : Snake m) (r : Nat) (hr : r+4≤m)
    (h1 : localAlpha p ⟨r+1,by omega⟩=2)
    (h2 : localAlpha p ⟨r+2,by omega⟩=2)
    (h3 : localAlpha p ⟨r+3,by omega⟩=2) :
    ∃h : NormalizedThreeCenters
      (translate p (p.vertex ⟨r+1,by omega⟩))
      ⟨r+1,by omega⟩ ⟨r+2,by omega⟩ ⟨r+3,by omega⟩,
      h.c≠h.d := by
  obtain ⟨h⟩ := normalize_five_vertex_window p r hr
  refine ⟨h,?_⟩
  intro hcd
  let q := translate p (p.vertex ⟨r+1,by omega⟩)
  have ha1 : localAlpha q ⟨r+1,by omega⟩=2 := (localAlpha_translate p _ _).trans h1
  have ha2 : localAlpha q ⟨r+2,by omega⟩=2 := (localAlpha_translate p _ _).trans h2
  have ha3 : localAlpha q ⟨r+3,by omega⟩=2 := (localAlpha_translate p _ _).trans h3
  have hs : InPath q (triple h.a h.b h.c) := by rw [hcd]; exact h.after_selected
  exact repeated_three_twos_impossible q h.a h.b h.c h.hab h.hac h.hbc
    _ _ _ h.left_eq h.middle_eq h.right_eq h.before_selected hs ha1 ha2 ha3

#print axioms normalize_five_vertex_window
#print axioms normalize_three_twos_to_distinct_window
end
end Snake9
