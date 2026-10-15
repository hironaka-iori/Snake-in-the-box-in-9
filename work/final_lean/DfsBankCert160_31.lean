import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_6 : search (oriented 6)[159]! (banFrom (fun i => (oriented 6)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_73 : search (oriented 73)[159]! (banFrom (fun i => (oriented 73)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_88 : search (oriented 88)[159]! (banFrom (fun i => (oriented 88)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_108 : search (oriented 108)[159]! (banFrom (fun i => (oriented 108)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_118 : search (oriented 118)[159]! (banFrom (fun i => (oriented 118)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_157 : search (oriented 157)[159]! (banFrom (fun i => (oriented 157)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_174 : search (oriented 174)[159]! (banFrom (fun i => (oriented 174)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_197 : search (oriented 197)[159]! (banFrom (fun i => (oriented 197)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_210 : search (oriented 210)[159]! (banFrom (fun i => (oriented 210)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_217_3_2_1_3_4_0 : search (((((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ^^^ 2 ^ 0) (((((((banFrom (fun i => (oriented 217)[i]!) 159) ||| cnMask (oriented 217)[159]!) ||| cnMask ((oriented 217)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) ||| cnMask ((((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4)) 27 = false := by decide +kernel
theorem keep160_217_3_2_1_3_4_2 : search (((((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ^^^ 2 ^ 2) (((((((banFrom (fun i => (oriented 217)[i]!) 159) ||| cnMask (oriented 217)[159]!) ||| cnMask ((oriented 217)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) ||| cnMask ((((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4)) 27 = false := by decide +kernel
theorem keep160_217_3_2_1_3_4 : search ((((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 217)[i]!) 159) ||| cnMask (oriented 217)[159]!) ||| cnMask ((oriented 217)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 28 = false :=
  search_of_children ((((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 217)[i]!) 159) ||| cnMask (oriented 217)[159]!) ||| cnMask ((oriented 217)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_217_3_2_1_3_4_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_217_3_2_1_3_4_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_217_3_2_1_3 : search (((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 217)[i]!) 159) ||| cnMask (oriented 217)[159]!) ||| cnMask ((oriented 217)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 217)[i]!) 159) ||| cnMask (oriented 217)[159]!) ||| cnMask ((oriented 217)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_217_3_2_1_3_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_217_3_2_1 : search ((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 217)[i]!) 159) ||| cnMask (oriented 217)[159]!) ||| cnMask ((oriented 217)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 30 = false :=
  search_of_children ((((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 217)[i]!) 159) ||| cnMask (oriented 217)[159]!) ||| cnMask ((oriented 217)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_217_3_2_1_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_217_3_2 : search (((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 217)[i]!) 159) ||| cnMask (oriented 217)[159]!) ||| cnMask ((oriented 217)[159]! ^^^ 2 ^ 3)) 31 = false :=
  search_of_children (((oriented 217)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 217)[i]!) 159) ||| cnMask (oriented 217)[159]!) ||| cnMask ((oriented 217)[159]! ^^^ 2 ^ 3)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_217_3_2_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_217_3 : search ((oriented 217)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 217)[i]!) 159) ||| cnMask (oriented 217)[159]!) 32 = false :=
  search_of_children ((oriented 217)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 217)[i]!) 159) ||| cnMask (oriented 217)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_217_3_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_217 : search (oriented 217)[159]! (banFrom (fun i => (oriented 217)[i]!) 159) 33 = false :=
  search_of_children (oriented 217)[159]! (banFrom (fun i => (oriented 217)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_217_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))

end Snake9.Dfs
