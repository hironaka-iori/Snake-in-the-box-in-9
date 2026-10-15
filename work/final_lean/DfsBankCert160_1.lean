import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_52_8_0 : search (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 0) (((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_52_8_1_2 : search ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1) ^^^ 2 ^ 2) ((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1)) 30 = false := by decide +kernel
theorem keep160_52_8_1_3_2 : search (((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1)) ||| cnMask ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 29 = false := by decide +kernel
theorem keep160_52_8_1_3_6 : search (((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 6) (((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1)) ||| cnMask ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 29 = false := by decide +kernel
theorem keep160_52_8_1_3 : search ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1)) 30 = false :=
  search_of_children ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_52_8_1_3_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_52_8_1_3_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_52_8_1 : search (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1) (((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) 31 = false :=
  search_of_children (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1) (((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_52_8_1_2
    | 3, _ => exact Or.inr keep160_52_8_1_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_52_8_4_6_1 : search (((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) ^^^ 2 ^ 6) ^^^ 2 ^ 1) (((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) ^^^ 2 ^ 6)) 29 = false := by decide +kernel
theorem keep160_52_8_4_6_2 : search (((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) ^^^ 2 ^ 6) ^^^ 2 ^ 2) (((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) ^^^ 2 ^ 6)) 29 = false := by decide +kernel
theorem keep160_52_8_4_6_3 : search (((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) ^^^ 2 ^ 6) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) ^^^ 2 ^ 6)) 29 = false := by decide +kernel
theorem keep160_52_8_4_6_8 : search (((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) ^^^ 2 ^ 6) ^^^ 2 ^ 8) (((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) ^^^ 2 ^ 6)) 29 = false := by decide +kernel
theorem keep160_52_8_4_6 : search ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) ^^^ 2 ^ 6) ((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4)) 30 = false :=
  search_of_children ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) ^^^ 2 ^ 6) ((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_52_8_4_6_1
    | 2, _ => exact Or.inr keep160_52_8_4_6_2
    | 3, _ => exact Or.inr keep160_52_8_4_6_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_52_8_4_6_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_52_8_4 : search (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) 31 = false :=
  search_of_children (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_52_8_4_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_52_8_6_2_0 : search (((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 2) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6)) ||| cnMask ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 2)) 29 = false := by decide +kernel
theorem keep160_52_8_6_2_4 : search (((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 2) ^^^ 2 ^ 4) (((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6)) ||| cnMask ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 2)) 29 = false := by decide +kernel
theorem keep160_52_8_6_2 : search ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 2) ((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6)) 30 = false :=
  search_of_children ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 2) ((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_52_8_6_2_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_52_8_6_2_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_52_8_6_4_1 : search (((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 4) ^^^ 2 ^ 1) (((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6)) ||| cnMask ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 4)) 29 = false := by decide +kernel
theorem keep160_52_8_6_4_2 : search (((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 4) ^^^ 2 ^ 2) (((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6)) ||| cnMask ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 4)) 29 = false := by decide +kernel
theorem keep160_52_8_6_4_3 : search (((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 4) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6)) ||| cnMask ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 4)) 29 = false := by decide +kernel
theorem keep160_52_8_6_4_8 : search (((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 4) ^^^ 2 ^ 8) (((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6)) ||| cnMask ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 4)) 29 = false := by decide +kernel
theorem keep160_52_8_6_4 : search ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 4) ((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6)) 30 = false :=
  search_of_children ((((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) ^^^ 2 ^ 4) ((((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_52_8_6_4_1
    | 2, _ => exact Or.inr keep160_52_8_6_4_2
    | 3, _ => exact Or.inr keep160_52_8_6_4_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_52_8_6_4_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_52_8_6 : search (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) (((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) 31 = false :=
  search_of_children (((oriented 52)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) (((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) ||| cnMask ((oriented 52)[159]! ^^^ 2 ^ 8)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_52_8_6_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_52_8_6_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_52_8 : search ((oriented 52)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) 32 = false :=
  search_of_children ((oriented 52)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 52)[i]!) 159) ||| cnMask (oriented 52)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_52_8_0
    | 1, _ => exact Or.inr keep160_52_8_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_52_8_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_52_8_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_52 : search (oriented 52)[159]! (banFrom (fun i => (oriented 52)[i]!) 159) 33 = false :=
  search_of_children (oriented 52)[159]! (banFrom (fun i => (oriented 52)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_52_8
    | n + 9, h => exact absurd h (by omega))

end Snake9.Dfs
