import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_12 : search (oriented 12)[159]! (banFrom (fun i => (oriented 12)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_33 : search (oriented 33)[159]! (banFrom (fun i => (oriented 33)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_39 : search (oriented 39)[159]! (banFrom (fun i => (oriented 39)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_58 : search (oriented 58)[159]! (banFrom (fun i => (oriented 58)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_86 : search (oriented 86)[159]! (banFrom (fun i => (oriented 86)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_137_3 : search ((oriented 137)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 137)[i]!) 159) ||| cnMask (oriented 137)[159]!) 32 = false := by decide +kernel
theorem keep160_137_8 : search ((oriented 137)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 137)[i]!) 159) ||| cnMask (oriented 137)[159]!) 32 = false := by decide +kernel
theorem keep160_137 : search (oriented 137)[159]! (banFrom (fun i => (oriented 137)[i]!) 159) 33 = false :=
  search_of_children (oriented 137)[159]! (banFrom (fun i => (oriented 137)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_137_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_137_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_140 : search (oriented 140)[159]! (banFrom (fun i => (oriented 140)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_189 : search (oriented 189)[159]! (banFrom (fun i => (oriented 189)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_191_0_4_1_0_2_3 : search (((((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ^^^ 2 ^ 3) (((((((banFrom (fun i => (oriented 191)[i]!) 159) ||| cnMask (oriented 191)[159]!) ||| cnMask ((oriented 191)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) ||| cnMask ((((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2)) 27 = false := by decide +kernel
theorem keep160_191_0_4_1_0_2_4 : search (((((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ^^^ 2 ^ 4) (((((((banFrom (fun i => (oriented 191)[i]!) 159) ||| cnMask (oriented 191)[159]!) ||| cnMask ((oriented 191)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) ||| cnMask ((((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2)) 27 = false := by decide +kernel
theorem keep160_191_0_4_1_0_2 : search ((((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 191)[i]!) 159) ||| cnMask (oriented 191)[159]!) ||| cnMask ((oriented 191)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false :=
  search_of_children ((((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 191)[i]!) 159) ||| cnMask (oriented 191)[159]!) ||| cnMask ((oriented 191)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_191_0_4_1_0_2_3
    | 4, _ => exact Or.inr keep160_191_0_4_1_0_2_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_191_0_4_1_0 : search (((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 191)[i]!) 159) ||| cnMask (oriented 191)[159]!) ||| cnMask ((oriented 191)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 191)[i]!) 159) ||| cnMask (oriented 191)[159]!) ||| cnMask ((oriented 191)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_191_0_4_1_0_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_191_0_4_1 : search ((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 191)[i]!) 159) ||| cnMask (oriented 191)[159]!) ||| cnMask ((oriented 191)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 30 = false :=
  search_of_children ((((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 191)[i]!) 159) ||| cnMask (oriented 191)[159]!) ||| cnMask ((oriented 191)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_191_0_4_1_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_191_0_4 : search (((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 191)[i]!) 159) ||| cnMask (oriented 191)[159]!) ||| cnMask ((oriented 191)[159]! ^^^ 2 ^ 0)) 31 = false :=
  search_of_children (((oriented 191)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 191)[i]!) 159) ||| cnMask (oriented 191)[159]!) ||| cnMask ((oriented 191)[159]! ^^^ 2 ^ 0)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_191_0_4_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_191_0 : search ((oriented 191)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 191)[i]!) 159) ||| cnMask (oriented 191)[159]!) 32 = false :=
  search_of_children ((oriented 191)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 191)[i]!) 159) ||| cnMask (oriented 191)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_191_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_191 : search (oriented 191)[159]! (banFrom (fun i => (oriented 191)[i]!) 159) 33 = false :=
  search_of_children (oriented 191)[159]! (banFrom (fun i => (oriented 191)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_191_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))

end Snake9.Dfs
