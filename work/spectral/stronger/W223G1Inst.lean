import W223G1Snake
import W223G1Data
/-!
# G1 instances: a normalised (2,2,3) window gives `Hyp` for the two window CNF tables

If the snake `q` runs through `0, 1, 3, 7, x` at positions `r..r+4` (with `x = 6` for the
"repeated direction" window and `x = 15` for the "distinct direction" window) and the local
singleton counts at `1, 3, 7` are `2, 2, 3`, then `sel q` satisfies `Hyp tabRep` resp.
`Hyp tabDis`.
-/
namespace W223G1
open Snake9 Snake9.SquareIncidence WinCNF
open Classical

noncomputable section

variable {m : Nat} (q : Snake m)

theorem center_counts (i ip inx : Fin (m+1)) (hip : ip.val + 1 = i.val)
    (hin : inx.val = i.val + 1) (c : Vertex) (u1 u2 : Coord) (hc : q.vertex i = c)
    (hp : q.vertex ip = flip u1 c) (hn : q.vertex inx = flip u2 c) (cs : List Nat)
    (hcs : (freePairs u1 u2).image (cornerOf c.val) = cs.toFinset)
    (hinj : ∀ a ∈ freePairs u1 u2, ∀ b ∈ freePairs u1 u2, cornerOf c.val a = cornerOf c.val b → a = b)
    (hnd : cs.Nodup) (hlen : cs.length = 21) (α : Nat) (hα : localAlpha q i = α) :
    (cs.filter (fun x => !sel q x)).length = α ∧ (cs.filter (sel q)).length = 21 - α := by
  subst hc
  have h := localAlpha_eq_corners q i ip inx hip hin u1 u2 hp hn cs hcs hinj hnd
  have hsplit := List.length_eq_length_filter_add (l := cs) (sel q)
  constructor <;> omega

theorem block_neg_bound {T : Tables} {S : Nat → Bool} (b : Block) (cs : List Nat)
    (hall : b.lits.all (negBall T) = true) (hmap : b.lits.map (litV T) = cs)
    (h : (cs.filter (fun x => !S x)).length ≤ b.k) : cnt (baseVal T S) b.lits ≤ b.k := by
  rw [cnt_negBall_eq hall, hmap]; exact h

theorem block_pos_bound {T : Tables} {S : Nat → Bool} (b : Block) (cs : List Nat)
    (hall : b.lits.all (posBall T) = true) (hmap : b.lits.map (litV T) = cs)
    (h : (cs.filter S).length ≤ b.k) : cnt (baseVal T S) b.lits ≤ b.k := by
  rw [cnt_posBall_eq hall, hmap]; exact h

theorem block_end_bound {T : Tables} (b : Block) (hall : b.lits.all (posEnd T) = true)
    (hmap : b.lits.map (litE T) = endsL) (hk : b.k = 2) :
    cnt (baseVal T (sel q)) b.lits ≤ b.k := by
  rw [cnt_posEnd_eq hall, hmap, hk]
  exact endSem_count q endsL (nodupB_nodup (by decide +kernel))

/-! ### Kernel-checked table facts -/

theorem cv1 : (freePairs 0 1).image (cornerOf 1) = (cornerVerts 1 0 1).toFinset := by decide +kernel
theorem cv3 : (freePairs 1 2).image (cornerOf 3) = (cornerVerts 3 1 2).toFinset := by decide +kernel
theorem cv7r : (freePairs 2 0).image (cornerOf 7) = (cornerVerts 7 2 0).toFinset := by decide +kernel
theorem cv7d : (freePairs 2 3).image (cornerOf 7) = (cornerVerts 7 2 3).toFinset := by decide +kernel
theorem inj1 : ∀ a ∈ freePairs 0 1, ∀ b ∈ freePairs 0 1, cornerOf 1 a = cornerOf 1 b → a = b := by
  decide +kernel
theorem inj3 : ∀ a ∈ freePairs 1 2, ∀ b ∈ freePairs 1 2, cornerOf 3 a = cornerOf 3 b → a = b := by
  decide +kernel
theorem inj7r : ∀ a ∈ freePairs 2 0, ∀ b ∈ freePairs 2 0, cornerOf 7 a = cornerOf 7 b → a = b := by
  decide +kernel
theorem inj7d : ∀ a ∈ freePairs 2 3, ∀ b ∈ freePairs 2 3, cornerOf 7 a = cornerOf 7 b → a = b := by
  decide +kernel
theorem nd1 : nodupB (cornerVerts 1 0 1) = true ∧ (cornerVerts 1 0 1).length = 21 := by decide +kernel
theorem nd3 : nodupB (cornerVerts 3 1 2) = true ∧ (cornerVerts 3 1 2).length = 21 := by decide +kernel
theorem nd7r : nodupB (cornerVerts 7 2 0) = true ∧ (cornerVerts 7 2 0).length = 21 := by decide +kernel
theorem nd7d : nodupB (cornerVerts 7 2 3) = true ∧ (cornerVerts 7 2 3).length = 21 := by decide +kernel

theorem repB_facts :
    repB0.lits.all (posEnd tabRep) = true ∧ repB0.lits.map (litE tabRep) = endsL ∧ repB0.k = 2 ∧
    repB1.lits.all (negBall tabRep) = true ∧ repB1.lits.map (litV tabRep) = cornerVerts 1 0 1 ∧
    repB1.k = 2 ∧
    repB2.lits.all (posBall tabRep) = true ∧ repB2.lits.map (litV tabRep) = cornerVerts 1 0 1 ∧
    repB2.k = 19 ∧
    repB3.lits.all (negBall tabRep) = true ∧ repB3.lits.map (litV tabRep) = cornerVerts 3 1 2 ∧
    repB3.k = 2 ∧
    repB4.lits.all (posBall tabRep) = true ∧ repB4.lits.map (litV tabRep) = cornerVerts 3 1 2 ∧
    repB4.k = 19 ∧
    repB5.lits.all (negBall tabRep) = true ∧ repB5.lits.map (litV tabRep) = cornerVerts 7 2 0 ∧
    repB5.k = 3 ∧
    repB6.lits.all (posBall tabRep) = true ∧ repB6.lits.map (litV tabRep) = cornerVerts 7 2 0 ∧
    repB6.k = 18 := by decide +kernel

theorem disB_facts :
    disB0.lits.all (posEnd tabDis) = true ∧ disB0.lits.map (litE tabDis) = endsL ∧ disB0.k = 2 ∧
    disB1.lits.all (negBall tabDis) = true ∧ disB1.lits.map (litV tabDis) = cornerVerts 1 0 1 ∧
    disB1.k = 2 ∧
    disB2.lits.all (posBall tabDis) = true ∧ disB2.lits.map (litV tabDis) = cornerVerts 1 0 1 ∧
    disB2.k = 19 ∧
    disB3.lits.all (negBall tabDis) = true ∧ disB3.lits.map (litV tabDis) = cornerVerts 3 1 2 ∧
    disB3.k = 2 ∧
    disB4.lits.all (posBall tabDis) = true ∧ disB4.lits.map (litV tabDis) = cornerVerts 3 1 2 ∧
    disB4.k = 19 ∧
    disB5.lits.all (negBall tabDis) = true ∧ disB5.lits.map (litV tabDis) = cornerVerts 7 2 3 ∧
    disB5.k = 3 ∧
    disB6.lits.all (posBall tabDis) = true ∧ disB6.lits.map (litV tabDis) = cornerVerts 7 2 3 ∧
    disB6.k = 18 := by decide +kernel

/-! ### The common window part -/

/-- The facts shared by both windows: vertex membership, local counts at the centres. -/
theorem window_common (r : Nat) (hr : r + 4 ≤ m) (x : Vertex) (u3 : Coord)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = x) (hx : x = flip u3 7)
    (a1 : localAlpha q ⟨r+1, by omega⟩ = 2) (a2 : localAlpha q ⟨r+2, by omega⟩ = 2)
    (a3 : localAlpha q ⟨r+3, by omega⟩ = 3)
    (cs7 : List Nat) (hcs7 : (freePairs 2 u3).image (cornerOf 7) = cs7.toFinset)
    (hinj7 : ∀ a ∈ freePairs 2 u3, ∀ b ∈ freePairs 2 u3, cornerOf 7 a = cornerOf 7 b → a = b)
    (hnd7 : nodupB cs7 = true ∧ cs7.length = 21) :
    (∀ w ∈ [0, 1, 3, 7, x.val], sel q w = true) ∧
    ((cornerVerts 1 0 1).filter (fun x => !sel q x)).length = 2 ∧
    ((cornerVerts 1 0 1).filter (sel q)).length = 19 ∧
    ((cornerVerts 3 1 2).filter (fun x => !sel q x)).length = 2 ∧
    ((cornerVerts 3 1 2).filter (sel q)).length = 19 ∧
    (cs7.filter (fun x => !sel q x)).length = 3 ∧
    (cs7.filter (sel q)).length = 18 := by
  have e1 := center_counts q ⟨r+1, by omega⟩ ⟨r, by omega⟩ ⟨r+2, by omega⟩ rfl rfl 1 0 1 h1
    (by rw [h0]; decide) (by rw [h2]; decide) _ cv1 inj1 (nodupB_nodup nd1.1) nd1.2 2 a1
  have e2 := center_counts q ⟨r+2, by omega⟩ ⟨r+1, by omega⟩ ⟨r+3, by omega⟩ rfl rfl 3 1 2 h2
    (by rw [h1]; decide) (by rw [h3]; decide) _ cv3 inj3 (nodupB_nodup nd3.1) nd3.2 2 a2
  have e3 := center_counts q ⟨r+3, by omega⟩ ⟨r+2, by omega⟩ ⟨r+4, by omega⟩ rfl rfl 7 2 u3 h3
    (by rw [h2]; decide) (by rw [h4, hx]) _ hcs7 hinj7 (nodupB_nodup hnd7.1) hnd7.2 3 a3
  refine ⟨?_, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2⟩
  intro w hw
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · have := sel_vertex q ⟨r, by omega⟩; rwa [h0] at this
  · have := sel_vertex q ⟨r+1, by omega⟩; rwa [h1] at this
  · have := sel_vertex q ⟨r+2, by omega⟩; rwa [h2] at this
  · have := sel_vertex q ⟨r+3, by omega⟩; rwa [h3] at this
  · have := sel_vertex q ⟨r+4, by omega⟩; rwa [h4] at this

theorem hyp_rep (r : Nat) (hr : r + 4 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = 6)
    (a1 : localAlpha q ⟨r+1, by omega⟩ = 2) (a2 : localAlpha q ⟨r+2, by omega⟩ = 2)
    (a3 : localAlpha q ⟨r+3, by omega⟩ = 3) : Hyp tabRep (sel q) := by
  obtain ⟨hw, c1, c1', c3, c3', c7, c7'⟩ := window_common q r hr 6 0 h0 h1 h2 h3 h4
    (by decide) a1 a2 a3 _ cv7r inj7r nd7r
  obtain ⟨f0, g0, k0, f1, g1, k1, f2, g2, k2, f3, g3, k3, f4, g4, k4, f5, g5, k5, f6, g6, k6⟩ :=
    repB_facts
  refine ⟨hw, sel_bad q, sel_deg q (by omega), ?_⟩
  intro b hb
  simp only [tabRep, blocksRep, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact block_end_bound q _ f0 g0 k0
  · exact block_neg_bound _ _ f1 g1 (by rw [k1, c1])
  · exact block_pos_bound _ _ f2 g2 (by rw [k2, c1'])
  · exact block_neg_bound _ _ f3 g3 (by rw [k3, c3])
  · exact block_pos_bound _ _ f4 g4 (by rw [k4, c3'])
  · exact block_neg_bound _ _ f5 g5 (by rw [k5, c7])
  · exact block_pos_bound _ _ f6 g6 (by rw [k6, c7'])

theorem hyp_dis (r : Nat) (hr : r + 4 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = 15)
    (a1 : localAlpha q ⟨r+1, by omega⟩ = 2) (a2 : localAlpha q ⟨r+2, by omega⟩ = 2)
    (a3 : localAlpha q ⟨r+3, by omega⟩ = 3) : Hyp tabDis (sel q) := by
  obtain ⟨hw, c1, c1', c3, c3', c7, c7'⟩ := window_common q r hr 15 3 h0 h1 h2 h3 h4
    (by decide) a1 a2 a3 _ cv7d inj7d nd7d
  obtain ⟨f0, g0, k0, f1, g1, k1, f2, g2, k2, f3, g3, k3, f4, g4, k4, f5, g5, k5, f6, g6, k6⟩ :=
    disB_facts
  refine ⟨hw, sel_bad q, sel_deg q (by omega), ?_⟩
  intro b hb
  simp only [tabDis, blocksDis, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact block_end_bound q _ f0 g0 k0
  · exact block_neg_bound _ _ f1 g1 (by rw [k1, c1])
  · exact block_pos_bound _ _ f2 g2 (by rw [k2, c1'])
  · exact block_neg_bound _ _ f3 g3 (by rw [k3, c3])
  · exact block_pos_bound _ _ f4 g4 (by rw [k4, c3'])
  · exact block_neg_bound _ _ f5 g5 (by rw [k5, c7])
  · exact block_pos_bound _ _ f6 g6 (by rw [k6, c7'])

end

end W223G1
