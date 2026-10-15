import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_74_2 : search ((oriented 74)[159]! ^^^ 2 ^ 2) ((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) 32 = false := by decide +kernel
theorem keep160_74_3_2_1_3_4_0 : search (((((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ^^^ 2 ^ 0) (((((((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) ||| cnMask ((oriented 74)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) ||| cnMask ((((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4)) 27 = false := by decide +kernel
theorem keep160_74_3_2_1_3_4_2 : search (((((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ^^^ 2 ^ 2) (((((((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) ||| cnMask ((oriented 74)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) ||| cnMask ((((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4)) 27 = false := by decide +kernel
theorem keep160_74_3_2_1_3_4 : search ((((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) ||| cnMask ((oriented 74)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 28 = false :=
  search_of_children ((((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) ||| cnMask ((oriented 74)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_74_3_2_1_3_4_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_74_3_2_1_3_4_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_74_3_2_1_3 : search (((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) ||| cnMask ((oriented 74)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) ||| cnMask ((oriented 74)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_74_3_2_1_3_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_74_3_2_1 : search ((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) ||| cnMask ((oriented 74)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 30 = false :=
  search_of_children ((((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) ||| cnMask ((oriented 74)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_74_3_2_1_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_74_3_2 : search (((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) ||| cnMask ((oriented 74)[159]! ^^^ 2 ^ 3)) 31 = false :=
  search_of_children (((oriented 74)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) ||| cnMask ((oriented 74)[159]! ^^^ 2 ^ 3)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_74_3_2_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_74_3 : search ((oriented 74)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) 32 = false :=
  search_of_children ((oriented 74)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 74)[i]!) 159) ||| cnMask (oriented 74)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_74_3_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_74 : search (oriented 74)[159]! (banFrom (fun i => (oriented 74)[i]!) 159) 33 = false :=
  search_of_children (oriented 74)[159]! (banFrom (fun i => (oriented 74)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_74_2
    | 3, _ => exact Or.inr keep160_74_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_97 : search (oriented 97)[159]! (banFrom (fun i => (oriented 97)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_98 : search (oriented 98)[159]! (banFrom (fun i => (oriented 98)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_151 : search (oriented 151)[159]! (banFrom (fun i => (oriented 151)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_168 : search (oriented 168)[159]! (banFrom (fun i => (oriented 168)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_188 : search (oriented 188)[159]! (banFrom (fun i => (oriented 188)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_194 : search (oriented 194)[159]! (banFrom (fun i => (oriented 194)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_216 : search (oriented 216)[159]! (banFrom (fun i => (oriented 216)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_223 : search (oriented 223)[159]! (banFrom (fun i => (oriented 223)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_241 : search (oriented 241)[159]! (banFrom (fun i => (oriented 241)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
