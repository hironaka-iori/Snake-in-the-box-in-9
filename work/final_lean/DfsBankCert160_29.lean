import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_4 : search (oriented 4)[159]! (banFrom (fun i => (oriented 4)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_93 : search (oriented 93)[159]! (banFrom (fun i => (oriented 93)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_126 : search (oriented 126)[159]! (banFrom (fun i => (oriented 126)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_135_3 : search ((oriented 135)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 135)[i]!) 159) ||| cnMask (oriented 135)[159]!) 32 = false := by decide +kernel
theorem keep160_135_8 : search ((oriented 135)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 135)[i]!) 159) ||| cnMask (oriented 135)[159]!) 32 = false := by decide +kernel
theorem keep160_135 : search (oriented 135)[159]! (banFrom (fun i => (oriented 135)[i]!) 159) 33 = false :=
  search_of_children (oriented 135)[159]! (banFrom (fun i => (oriented 135)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_135_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_135_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_163 : search (oriented 163)[159]! (banFrom (fun i => (oriented 163)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_198_3_2_1_3_4_0 : search (((((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ^^^ 2 ^ 0) (((((((banFrom (fun i => (oriented 198)[i]!) 159) ||| cnMask (oriented 198)[159]!) ||| cnMask ((oriented 198)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) ||| cnMask ((((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4)) 27 = false := by decide +kernel
theorem keep160_198_3_2_1_3_4_2 : search (((((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ^^^ 2 ^ 2) (((((((banFrom (fun i => (oriented 198)[i]!) 159) ||| cnMask (oriented 198)[159]!) ||| cnMask ((oriented 198)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) ||| cnMask ((((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4)) 27 = false := by decide +kernel
theorem keep160_198_3_2_1_3_4 : search ((((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 198)[i]!) 159) ||| cnMask (oriented 198)[159]!) ||| cnMask ((oriented 198)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 28 = false :=
  search_of_children ((((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 198)[i]!) 159) ||| cnMask (oriented 198)[159]!) ||| cnMask ((oriented 198)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_198_3_2_1_3_4_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_198_3_2_1_3_4_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_198_3_2_1_3 : search (((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 198)[i]!) 159) ||| cnMask (oriented 198)[159]!) ||| cnMask ((oriented 198)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 198)[i]!) 159) ||| cnMask (oriented 198)[159]!) ||| cnMask ((oriented 198)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_198_3_2_1_3_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_198_3_2_1 : search ((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 198)[i]!) 159) ||| cnMask (oriented 198)[159]!) ||| cnMask ((oriented 198)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 30 = false :=
  search_of_children ((((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 198)[i]!) 159) ||| cnMask (oriented 198)[159]!) ||| cnMask ((oriented 198)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_198_3_2_1_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_198_3_2 : search (((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 198)[i]!) 159) ||| cnMask (oriented 198)[159]!) ||| cnMask ((oriented 198)[159]! ^^^ 2 ^ 3)) 31 = false :=
  search_of_children (((oriented 198)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 198)[i]!) 159) ||| cnMask (oriented 198)[159]!) ||| cnMask ((oriented 198)[159]! ^^^ 2 ^ 3)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_198_3_2_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_198_3 : search ((oriented 198)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 198)[i]!) 159) ||| cnMask (oriented 198)[159]!) 32 = false :=
  search_of_children ((oriented 198)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 198)[i]!) 159) ||| cnMask (oriented 198)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_198_3_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_198 : search (oriented 198)[159]! (banFrom (fun i => (oriented 198)[i]!) 159) 33 = false :=
  search_of_children (oriented 198)[159]! (banFrom (fun i => (oriented 198)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_198_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_207 : search (oriented 207)[159]! (banFrom (fun i => (oriented 207)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_251 : search (oriented 251)[159]! (banFrom (fun i => (oriented 251)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_254 : search (oriented 254)[159]! (banFrom (fun i => (oriented 254)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
