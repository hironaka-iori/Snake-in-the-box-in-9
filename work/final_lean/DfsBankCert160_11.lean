import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_28 : search (oriented 28)[159]! (banFrom (fun i => (oriented 28)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_162 : search (oriented 162)[159]! (banFrom (fun i => (oriented 162)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_261_4_3_2_0_1 : search ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 1) ((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_261_4_3_2_0_3 : search ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_261_4_3_2_0_4 : search ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_261_4_3_2_0_7 : search ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_261_4_3_2_0 : search (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 29 = false :=
  search_of_children (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_261_4_3_2_0_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_261_4_3_2_0_3
    | 4, _ => exact Or.inr keep160_261_4_3_2_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_261_4_3_2_0_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_261_4_3_2 : search ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2) ((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) 30 = false :=
  search_of_children ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 2) ((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_261_4_3_2_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_261_4_3_7_1_5_2_0 : search ((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 0) ((((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1)) ||| cnMask ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5)) ||| cnMask (((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2)) 26 = false := by decide +kernel
theorem keep160_261_4_3_7_1_5_2_7_0_3 : search ((((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ((((((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1)) ||| cnMask ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5)) ||| cnMask (((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2)) ||| cnMask ((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7)) ||| cnMask (((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7) ^^^ 2 ^ 0)) 24 = false := by decide +kernel
theorem keep160_261_4_3_7_1_5_2_7_0_4 : search ((((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7) ^^^ 2 ^ 0) ^^^ 2 ^ 4) ((((((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1)) ||| cnMask ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5)) ||| cnMask (((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2)) ||| cnMask ((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7)) ||| cnMask (((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7) ^^^ 2 ^ 0)) 24 = false := by decide +kernel
theorem keep160_261_4_3_7_1_5_2_7_0_5 : search ((((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7) ^^^ 2 ^ 0) ^^^ 2 ^ 5) ((((((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1)) ||| cnMask ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5)) ||| cnMask (((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2)) ||| cnMask ((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7)) ||| cnMask (((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7) ^^^ 2 ^ 0)) 24 = false := by decide +kernel
theorem keep160_261_4_3_7_1_5_2_7_0 : search (((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7) ^^^ 2 ^ 0) (((((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1)) ||| cnMask ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5)) ||| cnMask (((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2)) ||| cnMask ((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7)) 25 = false :=
  search_of_children (((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7) ^^^ 2 ^ 0) (((((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1)) ||| cnMask ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5)) ||| cnMask (((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2)) ||| cnMask ((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7)) 24 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_261_4_3_7_1_5_2_7_0_3
    | 4, _ => exact Or.inr keep160_261_4_3_7_1_5_2_7_0_4
    | 5, _ => exact Or.inr keep160_261_4_3_7_1_5_2_7_0_5
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_261_4_3_7_1_5_2_7 : search ((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7) ((((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1)) ||| cnMask ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5)) ||| cnMask (((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2)) 26 = false :=
  search_of_children ((((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) ^^^ 2 ^ 7) ((((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1)) ||| cnMask ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5)) ||| cnMask (((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2)) 25 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_261_4_3_7_1_5_2_7_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_261_4_3_7_1_5_2 : search (((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) (((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1)) ||| cnMask ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5)) 27 = false :=
  search_of_children (((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ^^^ 2 ^ 2) (((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1)) ||| cnMask ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5)) 26 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_261_4_3_7_1_5_2_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_261_4_3_7_1_5_2_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_261_4_3_7_1_5 : search ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1)) 28 = false :=
  search_of_children ((((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ^^^ 2 ^ 5) ((((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) ||| cnMask (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_261_4_3_7_1_5_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_261_4_3_7_1 : search (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) (((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) 29 = false :=
  search_of_children (((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) (((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) ||| cnMask ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inr keep160_261_4_3_7_1_5
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_261_4_3_7 : search ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) 30 = false :=
  search_of_children ((((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ((((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_261_4_3_7_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_261_4_3 : search (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) (((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) 31 = false :=
  search_of_children (((oriented 261)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 3) (((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) ||| cnMask ((oriented 261)[159]! ^^^ 2 ^ 4)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_261_4_3_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_261_4_3_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_261_4 : search ((oriented 261)[159]! ^^^ 2 ^ 4) ((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) 32 = false :=
  search_of_children ((oriented 261)[159]! ^^^ 2 ^ 4) ((banFrom (fun i => (oriented 261)[i]!) 159) ||| cnMask (oriented 261)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_261_4_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_261 : search (oriented 261)[159]! (banFrom (fun i => (oriented 261)[i]!) 159) 33 = false :=
  search_of_children (oriented 261)[159]! (banFrom (fun i => (oriented 261)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_261_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))

end Snake9.Dfs
