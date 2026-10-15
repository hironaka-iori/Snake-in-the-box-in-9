import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_9 : search (oriented 9)[159]! (banFrom (fun i => (oriented 9)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_20 : search (oriented 20)[159]! (banFrom (fun i => (oriented 20)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_63 : search (oriented 63)[159]! (banFrom (fun i => (oriented 63)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_89 : search (oriented 89)[159]! (banFrom (fun i => (oriented 89)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_120 : search (oriented 120)[159]! (banFrom (fun i => (oriented 120)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_155 : search (oriented 155)[159]! (banFrom (fun i => (oriented 155)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_156 : search (oriented 156)[159]! (banFrom (fun i => (oriented 156)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_193 : search (oriented 193)[159]! (banFrom (fun i => (oriented 193)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_215_3_2_1_3_4_0 : search (((((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ^^^ 2 ^ 0) (((((((banFrom (fun i => (oriented 215)[i]!) 159) ||| cnMask (oriented 215)[159]!) ||| cnMask ((oriented 215)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) ||| cnMask ((((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4)) 27 = false := by decide +kernel
theorem keep160_215_3_2_1_3_4_2 : search (((((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ^^^ 2 ^ 2) (((((((banFrom (fun i => (oriented 215)[i]!) 159) ||| cnMask (oriented 215)[159]!) ||| cnMask ((oriented 215)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) ||| cnMask ((((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4)) 27 = false := by decide +kernel
theorem keep160_215_3_2_1_3_4 : search ((((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 215)[i]!) 159) ||| cnMask (oriented 215)[159]!) ||| cnMask ((oriented 215)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 28 = false :=
  search_of_children ((((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 215)[i]!) 159) ||| cnMask (oriented 215)[159]!) ||| cnMask ((oriented 215)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_215_3_2_1_3_4_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_215_3_2_1_3_4_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_215_3_2_1_3 : search (((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 215)[i]!) 159) ||| cnMask (oriented 215)[159]!) ||| cnMask ((oriented 215)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 215)[i]!) 159) ||| cnMask (oriented 215)[159]!) ||| cnMask ((oriented 215)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_215_3_2_1_3_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_215_3_2_1 : search ((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 215)[i]!) 159) ||| cnMask (oriented 215)[159]!) ||| cnMask ((oriented 215)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 30 = false :=
  search_of_children ((((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 215)[i]!) 159) ||| cnMask (oriented 215)[159]!) ||| cnMask ((oriented 215)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_215_3_2_1_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_215_3_2 : search (((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 215)[i]!) 159) ||| cnMask (oriented 215)[159]!) ||| cnMask ((oriented 215)[159]! ^^^ 2 ^ 3)) 31 = false :=
  search_of_children (((oriented 215)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 215)[i]!) 159) ||| cnMask (oriented 215)[159]!) ||| cnMask ((oriented 215)[159]! ^^^ 2 ^ 3)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_215_3_2_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_215_3 : search ((oriented 215)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 215)[i]!) 159) ||| cnMask (oriented 215)[159]!) 32 = false :=
  search_of_children ((oriented 215)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 215)[i]!) 159) ||| cnMask (oriented 215)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_215_3_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_215 : search (oriented 215)[159]! (banFrom (fun i => (oriented 215)[i]!) 159) 33 = false :=
  search_of_children (oriented 215)[159]! (banFrom (fun i => (oriented 215)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_215_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_233 : search (oriented 233)[159]! (banFrom (fun i => (oriented 233)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
