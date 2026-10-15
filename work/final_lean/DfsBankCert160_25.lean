import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_30 : search (oriented 30)[159]! (banFrom (fun i => (oriented 30)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_101 : search (oriented 101)[159]! (banFrom (fun i => (oriented 101)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_115_2 : search ((oriented 115)[159]! ^^^ 2 ^ 2) ((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) 32 = false := by decide +kernel
theorem keep160_115_3_2_1_3_4_0 : search (((((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ^^^ 2 ^ 0) (((((((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) ||| cnMask ((oriented 115)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) ||| cnMask ((((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4)) 27 = false := by decide +kernel
theorem keep160_115_3_2_1_3_4_2 : search (((((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ^^^ 2 ^ 2) (((((((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) ||| cnMask ((oriented 115)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) ||| cnMask ((((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4)) 27 = false := by decide +kernel
theorem keep160_115_3_2_1_3_4 : search ((((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) ||| cnMask ((oriented 115)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 28 = false :=
  search_of_children ((((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) ||| cnMask ((oriented 115)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_115_3_2_1_3_4_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_115_3_2_1_3_4_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_115_3_2_1_3 : search (((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) ||| cnMask ((oriented 115)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) ||| cnMask ((oriented 115)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_115_3_2_1_3_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_115_3_2_1 : search ((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) ||| cnMask ((oriented 115)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 30 = false :=
  search_of_children ((((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) ||| cnMask ((oriented 115)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_115_3_2_1_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_115_3_2 : search (((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) ||| cnMask ((oriented 115)[159]! ^^^ 2 ^ 3)) 31 = false :=
  search_of_children (((oriented 115)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) ||| cnMask ((oriented 115)[159]! ^^^ 2 ^ 3)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_115_3_2_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_115_3 : search ((oriented 115)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) 32 = false :=
  search_of_children ((oriented 115)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 115)[i]!) 159) ||| cnMask (oriented 115)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_115_3_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_115 : search (oriented 115)[159]! (banFrom (fun i => (oriented 115)[i]!) 159) 33 = false :=
  search_of_children (oriented 115)[159]! (banFrom (fun i => (oriented 115)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_115_2
    | 3, _ => exact Or.inr keep160_115_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_147 : search (oriented 147)[159]! (banFrom (fun i => (oriented 147)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_175 : search (oriented 175)[159]! (banFrom (fun i => (oriented 175)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_190 : search (oriented 190)[159]! (banFrom (fun i => (oriented 190)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_200 : search (oriented 200)[159]! (banFrom (fun i => (oriented 200)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_212 : search (oriented 212)[159]! (banFrom (fun i => (oriented 212)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_219 : search (oriented 219)[159]! (banFrom (fun i => (oriented 219)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_237 : search (oriented 237)[159]! (banFrom (fun i => (oriented 237)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
