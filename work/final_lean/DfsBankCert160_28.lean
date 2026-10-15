import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_16 : search (oriented 16)[159]! (banFrom (fun i => (oriented 16)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_35 : search (oriented 35)[159]! (banFrom (fun i => (oriented 35)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_60 : search (oriented 60)[159]! (banFrom (fun i => (oriented 60)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_141_3 : search ((oriented 141)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 141)[i]!) 159) ||| cnMask (oriented 141)[159]!) 32 = false := by decide +kernel
theorem keep160_141_8 : search ((oriented 141)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 141)[i]!) 159) ||| cnMask (oriented 141)[159]!) 32 = false := by decide +kernel
theorem keep160_141 : search (oriented 141)[159]! (banFrom (fun i => (oriented 141)[i]!) 159) 33 = false :=
  search_of_children (oriented 141)[159]! (banFrom (fun i => (oriented 141)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_141_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_141_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_149 : search (oriented 149)[159]! (banFrom (fun i => (oriented 149)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_182 : search (oriented 182)[159]! (banFrom (fun i => (oriented 182)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_195_0_4_1_0_2_3 : search (((((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ^^^ 2 ^ 3) (((((((banFrom (fun i => (oriented 195)[i]!) 159) ||| cnMask (oriented 195)[159]!) ||| cnMask ((oriented 195)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) ||| cnMask ((((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2)) 27 = false := by decide +kernel
theorem keep160_195_0_4_1_0_2_4 : search (((((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ^^^ 2 ^ 4) (((((((banFrom (fun i => (oriented 195)[i]!) 159) ||| cnMask (oriented 195)[159]!) ||| cnMask ((oriented 195)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) ||| cnMask ((((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2)) 27 = false := by decide +kernel
theorem keep160_195_0_4_1_0_2 : search ((((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 195)[i]!) 159) ||| cnMask (oriented 195)[159]!) ||| cnMask ((oriented 195)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false :=
  search_of_children ((((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 195)[i]!) 159) ||| cnMask (oriented 195)[159]!) ||| cnMask ((oriented 195)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_195_0_4_1_0_2_3
    | 4, _ => exact Or.inr keep160_195_0_4_1_0_2_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_195_0_4_1_0 : search (((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 195)[i]!) 159) ||| cnMask (oriented 195)[159]!) ||| cnMask ((oriented 195)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 195)[i]!) 159) ||| cnMask (oriented 195)[159]!) ||| cnMask ((oriented 195)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_195_0_4_1_0_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_195_0_4_1 : search ((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 195)[i]!) 159) ||| cnMask (oriented 195)[159]!) ||| cnMask ((oriented 195)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 30 = false :=
  search_of_children ((((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 195)[i]!) 159) ||| cnMask (oriented 195)[159]!) ||| cnMask ((oriented 195)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_195_0_4_1_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_195_0_4 : search (((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 195)[i]!) 159) ||| cnMask (oriented 195)[159]!) ||| cnMask ((oriented 195)[159]! ^^^ 2 ^ 0)) 31 = false :=
  search_of_children (((oriented 195)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 195)[i]!) 159) ||| cnMask (oriented 195)[159]!) ||| cnMask ((oriented 195)[159]! ^^^ 2 ^ 0)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_195_0_4_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_195_0 : search ((oriented 195)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 195)[i]!) 159) ||| cnMask (oriented 195)[159]!) 32 = false :=
  search_of_children ((oriented 195)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 195)[i]!) 159) ||| cnMask (oriented 195)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_195_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_195 : search (oriented 195)[159]! (banFrom (fun i => (oriented 195)[i]!) 159) 33 = false :=
  search_of_children (oriented 195)[159]! (banFrom (fun i => (oriented 195)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_195_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_199 : search (oriented 199)[159]! (banFrom (fun i => (oriented 199)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_235 : search (oriented 235)[159]! (banFrom (fun i => (oriented 235)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
