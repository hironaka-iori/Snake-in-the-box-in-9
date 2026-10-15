import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_64_0_2 : search (((oriented 64)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 64)[i]!) 159) ||| cnMask (oriented 64)[159]!) ||| cnMask ((oriented 64)[159]! ^^^ 2 ^ 0)) 31 = false := by decide +kernel
theorem keep160_64_0_4 : search (((oriented 64)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 64)[i]!) 159) ||| cnMask (oriented 64)[159]!) ||| cnMask ((oriented 64)[159]! ^^^ 2 ^ 0)) 31 = false := by decide +kernel
theorem keep160_64_0 : search ((oriented 64)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 64)[i]!) 159) ||| cnMask (oriented 64)[159]!) 32 = false :=
  search_of_children ((oriented 64)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 64)[i]!) 159) ||| cnMask (oriented 64)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_64_0_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_64_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_64_4 : search ((oriented 64)[159]! ^^^ 2 ^ 4) ((banFrom (fun i => (oriented 64)[i]!) 159) ||| cnMask (oriented 64)[159]!) 32 = false := by decide +kernel
theorem keep160_64 : search (oriented 64)[159]! (banFrom (fun i => (oriented 64)[i]!) 159) 33 = false :=
  search_of_children (oriented 64)[159]! (banFrom (fun i => (oriented 64)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_64_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_64_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_85_0_4_1_0_2 : search ((((((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 85)[i]!) 159) ||| cnMask (oriented 85)[159]!) ||| cnMask ((oriented 85)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_85_0_4_1_0_3 : search ((((((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ((((((banFrom (fun i => (oriented 85)[i]!) 159) ||| cnMask (oriented 85)[159]!) ||| cnMask ((oriented 85)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_85_0_4_1_0 : search (((((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 85)[i]!) 159) ||| cnMask (oriented 85)[159]!) ||| cnMask ((oriented 85)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 85)[i]!) 159) ||| cnMask (oriented 85)[159]!) ||| cnMask ((oriented 85)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_85_0_4_1_0_2
    | 3, _ => exact Or.inr keep160_85_0_4_1_0_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_85_0_4_1 : search ((((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 85)[i]!) 159) ||| cnMask (oriented 85)[159]!) ||| cnMask ((oriented 85)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 30 = false :=
  search_of_children ((((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 85)[i]!) 159) ||| cnMask (oriented 85)[159]!) ||| cnMask ((oriented 85)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_85_0_4_1_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_85_0_4 : search (((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 85)[i]!) 159) ||| cnMask (oriented 85)[159]!) ||| cnMask ((oriented 85)[159]! ^^^ 2 ^ 0)) 31 = false :=
  search_of_children (((oriented 85)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 85)[i]!) 159) ||| cnMask (oriented 85)[159]!) ||| cnMask ((oriented 85)[159]! ^^^ 2 ^ 0)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_85_0_4_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_85_0 : search ((oriented 85)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 85)[i]!) 159) ||| cnMask (oriented 85)[159]!) 32 = false :=
  search_of_children ((oriented 85)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 85)[i]!) 159) ||| cnMask (oriented 85)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_85_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_85 : search (oriented 85)[159]! (banFrom (fun i => (oriented 85)[i]!) 159) 33 = false :=
  search_of_children (oriented 85)[159]! (banFrom (fun i => (oriented 85)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_85_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_94 : search (oriented 94)[159]! (banFrom (fun i => (oriented 94)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_102 : search (oriented 102)[159]! (banFrom (fun i => (oriented 102)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_196 : search (oriented 196)[159]! (banFrom (fun i => (oriented 196)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_225 : search (oriented 225)[159]! (banFrom (fun i => (oriented 225)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_242 : search (oriented 242)[159]! (banFrom (fun i => (oriented 242)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_249 : search (oriented 249)[159]! (banFrom (fun i => (oriented 249)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
