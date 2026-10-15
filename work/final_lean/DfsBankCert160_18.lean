import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_3 : search (oriented 3)[159]! (banFrom (fun i => (oriented 3)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_27 : search (oriented 27)[159]! (banFrom (fun i => (oriented 27)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_67 : search (oriented 67)[159]! (banFrom (fun i => (oriented 67)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_72 : search (oriented 72)[159]! (banFrom (fun i => (oriented 72)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_78 : search (oriented 78)[159]! (banFrom (fun i => (oriented 78)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_134 : search (oriented 134)[159]! (banFrom (fun i => (oriented 134)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_148_4_3_1_2_3_0_7_1 : search (((((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ^^^ 2 ^ 1) (((((((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2)) ||| cnMask ((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3)) ||| cnMask (((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0)) ||| cnMask ((((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0) ^^^ 2 ^ 7)) 25 = false := by decide +kernel
theorem keep160_148_4_3_1_2_3_0_7_4 : search (((((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ^^^ 2 ^ 4) (((((((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2)) ||| cnMask ((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3)) ||| cnMask (((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0)) ||| cnMask ((((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0) ^^^ 2 ^ 7)) 25 = false := by decide +kernel
theorem keep160_148_4_3_1_2_3_0_7_8 : search (((((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ^^^ 2 ^ 8) (((((((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2)) ||| cnMask ((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3)) ||| cnMask (((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0)) ||| cnMask ((((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0) ^^^ 2 ^ 7)) 25 = false := by decide +kernel
theorem keep160_148_4_3_1_2_3_0_7 : search ((((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ((((((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2)) ||| cnMask ((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3)) ||| cnMask (((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0)) 26 = false :=
  search_of_children ((((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ((((((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2)) ||| cnMask ((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3)) ||| cnMask (((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0)) 25 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_148_4_3_1_2_3_0_7_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_148_4_3_1_2_3_0_7_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_148_4_3_1_2_3_0_7_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_148_4_3_1_2_3_0 : search (((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0) (((((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2)) ||| cnMask ((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3)) 27 = false :=
  search_of_children (((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ^^^ 2 ^ 0) (((((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2)) ||| cnMask ((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3)) 26 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_148_4_3_1_2_3_0_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_148_4_3_1_2_3 : search ((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ((((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2)) 28 = false :=
  search_of_children ((((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ^^^ 2 ^ 3) ((((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_148_4_3_1_2_3_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_148_4_3_1_2 : search (((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) (((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ^^^ 2 ^ 2) (((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_148_4_3_1_2_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_148_4_3_1 : search ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) 30 = false :=
  search_of_children ((((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_148_4_3_1_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_148_4_3 : search (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) (((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) 31 = false :=
  search_of_children (((oriented 148)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) (((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) ||| cnMask ((oriented 148)[159]! ^^^ 2 ^ 4)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_148_4_3_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_148_4 : search ((oriented 148)[159]! ^^^ 2 ^ 4) ((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) 32 = false :=
  search_of_children ((oriented 148)[159]! ^^^ 2 ^ 4) ((banFrom (fun i => (oriented 148)[i]!) 159) ||| cnMask (oriented 148)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_148_4_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_148 : search (oriented 148)[159]! (banFrom (fun i => (oriented 148)[i]!) 159) 33 = false :=
  search_of_children (oriented 148)[159]! (banFrom (fun i => (oriented 148)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_148_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_185 : search (oriented 185)[159]! (banFrom (fun i => (oriented 185)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_222 : search (oriented 222)[159]! (banFrom (fun i => (oriented 222)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
