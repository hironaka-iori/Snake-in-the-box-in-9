import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_1 : search (oriented 1)[159]! (banFrom (fun i => (oriented 1)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_25 : search (oriented 25)[159]! (banFrom (fun i => (oriented 25)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_53 : search (oriented 53)[159]! (banFrom (fun i => (oriented 53)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_62 : search (oriented 62)[159]! (banFrom (fun i => (oriented 62)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_65 : search (oriented 65)[159]! (banFrom (fun i => (oriented 65)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_130 : search (oriented 130)[159]! (banFrom (fun i => (oriented 130)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_165_2_0_1_4_0_3_7_1 : search (((((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) (((((((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4)) ||| cnMask ((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask (((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3)) ||| cnMask ((((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) 25 = false := by decide +kernel
theorem keep160_165_2_0_1_4_0_3_7_2 : search (((((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 2) (((((((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4)) ||| cnMask ((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask (((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3)) ||| cnMask ((((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) 25 = false := by decide +kernel
theorem keep160_165_2_0_1_4_0_3_7_6 : search (((((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 6) (((((((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4)) ||| cnMask ((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask (((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3)) ||| cnMask ((((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) 25 = false := by decide +kernel
theorem keep160_165_2_0_1_4_0_3_7 : search ((((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ((((((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4)) ||| cnMask ((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask (((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3)) 26 = false :=
  search_of_children ((((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ((((((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4)) ||| cnMask ((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask (((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3)) 25 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_165_2_0_1_4_0_3_7_1
    | 2, _ => exact Or.inr keep160_165_2_0_1_4_0_3_7_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_165_2_0_1_4_0_3_7_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_165_2_0_1_4_0_3 : search (((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) (((((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4)) ||| cnMask ((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0)) 27 = false :=
  search_of_children (((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) (((((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4)) ||| cnMask ((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0)) 26 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_165_2_0_1_4_0_3_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_165_2_0_1_4_0 : search ((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ((((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4)) 28 = false :=
  search_of_children ((((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) ^^^ 2 ^ 0) ((((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_165_2_0_1_4_0_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_165_2_0_1_4 : search (((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) (((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ^^^ 2 ^ 4) (((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_165_2_0_1_4_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_165_2_0_1 : search ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) 30 = false :=
  search_of_children ((((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) ||| cnMask (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_165_2_0_1_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_165_2_0 : search (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) (((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) 31 = false :=
  search_of_children (((oriented 165)[159]! ^^^ 2 ^ 2) ^^^ 2 ^ 0) (((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) ||| cnMask ((oriented 165)[159]! ^^^ 2 ^ 2)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_165_2_0_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_165_2 : search ((oriented 165)[159]! ^^^ 2 ^ 2) ((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) 32 = false :=
  search_of_children ((oriented 165)[159]! ^^^ 2 ^ 2) ((banFrom (fun i => (oriented 165)[i]!) 159) ||| cnMask (oriented 165)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_165_2_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_165 : search (oriented 165)[159]! (banFrom (fun i => (oriented 165)[i]!) 159) 33 = false :=
  search_of_children (oriented 165)[159]! (banFrom (fun i => (oriented 165)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_165_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_186 : search (oriented 186)[159]! (banFrom (fun i => (oriented 186)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_220 : search (oriented 220)[159]! (banFrom (fun i => (oriented 220)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
