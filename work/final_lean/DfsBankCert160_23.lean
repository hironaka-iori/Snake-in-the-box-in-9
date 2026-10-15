import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_70_0_4_1_0_2_3 : search (((((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ^^^ 2 ^ 3) (((((((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) ||| cnMask ((oriented 70)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) ||| cnMask ((((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2)) 27 = false := by decide +kernel
theorem keep160_70_0_4_1_0_2_4 : search (((((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ^^^ 2 ^ 4) (((((((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) ||| cnMask ((oriented 70)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) ||| cnMask ((((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2)) 27 = false := by decide +kernel
theorem keep160_70_0_4_1_0_2 : search ((((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) ||| cnMask ((oriented 70)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false :=
  search_of_children ((((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) ||| cnMask ((oriented 70)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_70_0_4_1_0_2_3
    | 4, _ => exact Or.inr keep160_70_0_4_1_0_2_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_70_0_4_1_0 : search (((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) ||| cnMask ((oriented 70)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) ||| cnMask ((oriented 70)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_70_0_4_1_0_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_70_0_4_1 : search ((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) ||| cnMask ((oriented 70)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 30 = false :=
  search_of_children ((((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) ||| cnMask ((oriented 70)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_70_0_4_1_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_70_0_4 : search (((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) ||| cnMask ((oriented 70)[159]! ^^^ 2 ^ 0)) 31 = false :=
  search_of_children (((oriented 70)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) ||| cnMask ((oriented 70)[159]! ^^^ 2 ^ 0)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_70_0_4_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_70_0 : search ((oriented 70)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) 32 = false :=
  search_of_children ((oriented 70)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_70_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_70_4 : search ((oriented 70)[159]! ^^^ 2 ^ 4) ((banFrom (fun i => (oriented 70)[i]!) 159) ||| cnMask (oriented 70)[159]!) 32 = false := by decide +kernel
theorem keep160_70 : search (oriented 70)[159]! (banFrom (fun i => (oriented 70)[i]!) 159) 33 = false :=
  search_of_children (oriented 70)[159]! (banFrom (fun i => (oriented 70)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_70_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_70_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_83 : search (oriented 83)[159]! (banFrom (fun i => (oriented 83)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_143 : search (oriented 143)[159]! (banFrom (fun i => (oriented 143)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_144 : search (oriented 144)[159]! (banFrom (fun i => (oriented 144)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_167 : search (oriented 167)[159]! (banFrom (fun i => (oriented 167)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_183 : search (oriented 183)[159]! (banFrom (fun i => (oriented 183)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_206 : search (oriented 206)[159]! (banFrom (fun i => (oriented 206)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_211 : search (oriented 211)[159]! (banFrom (fun i => (oriented 211)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_229 : search (oriented 229)[159]! (banFrom (fun i => (oriented 229)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
