import RegrowthParityCounts
namespace Snake9.Regrowth.E112041
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[186, 178, 182, 180, 188, 189, 173, 175, 167, 163, 161, 160, 168, 424, 425, 427, 443, 315, 314, 306, 310, 308, 316, 300, 301, 303, 295, 291, 289, 288, 352, 356, 358, 366, 362, 363, 361, 377, 381, 373, 375, 371, 115, 99, 103, 111, 109, 108, 124, 126, 62, 63, 55, 53, 37, 36, 38, 34, 42, 43, 41, 57, 56, 48, 112, 240, 248, 249, 233, 235, 234, 238, 230, 228, 229, 245, 247, 255, 511, 495, 493, 492, 508, 500, 502, 498, 482, 483, 481, 497, 433, 437, 421, 420, 422, 430, 446, 414, 158, 159, 151, 149, 145, 153, 137, 139, 138, 130, 134, 132, 140, 396]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (7 : Vertex), (8 : Vertex), (13 : Vertex), (14 : Vertex), (15 : Vertex), (18 : Vertex), (19 : Vertex), (20 : Vertex), (22 : Vertex), (26 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (64 : Vertex), (65 : Vertex), (66 : Vertex), (68 : Vertex), (69 : Vertex), (70 : Vertex), (72 : Vertex), (73 : Vertex), (74 : Vertex), (75 : Vertex), (78 : Vertex), (81 : Vertex), (82 : Vertex), (84 : Vertex), (85 : Vertex), (86 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (90 : Vertex), (91 : Vertex), (93 : Vertex), (95 : Vertex), (192 : Vertex), (193 : Vertex), (195 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (207 : Vertex), (210 : Vertex), (211 : Vertex), (212 : Vertex), (214 : Vertex), (218 : Vertex), (219 : Vertex), (220 : Vertex), (221 : Vertex), (258 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (273 : Vertex), (275 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (285 : Vertex), (287 : Vertex), (321 : Vertex), (322 : Vertex), (323 : Vertex), (325 : Vertex), (327 : Vertex), (328 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (338 : Vertex), (340 : Vertex), (342 : Vertex), (344 : Vertex), (346 : Vertex), (347 : Vertex), (348 : Vertex), (350 : Vertex), (351 : Vertex), (384 : Vertex), (385 : Vertex), (387 : Vertex), (391 : Vertex), (396 : Vertex), (397 : Vertex), (399 : Vertex), (400 : Vertex), (402 : Vertex), (403 : Vertex), (404 : Vertex), (408 : Vertex), (413 : Vertex), (448 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (8 : Vertex), (13 : Vertex), (14 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (64 : Vertex), (69 : Vertex), (70 : Vertex), (73 : Vertex), (74 : Vertex), (81 : Vertex), (82 : Vertex), (84 : Vertex), (87 : Vertex), (88 : Vertex), (91 : Vertex), (93 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (273 : Vertex), (279 : Vertex), (280 : Vertex), (285 : Vertex), (321 : Vertex), (322 : Vertex), (327 : Vertex), (328 : Vertex), (333 : Vertex), (336 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (351 : Vertex), (385 : Vertex), (391 : Vertex), (397 : Vertex), (400 : Vertex), (403 : Vertex), (448 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (471 : Vertex), (472 : Vertex), (475 : Vertex), (477 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (15 : Vertex), (18 : Vertex), (20 : Vertex), (27 : Vertex), (29 : Vertex), (65 : Vertex), (66 : Vertex), (68 : Vertex), (72 : Vertex), (75 : Vertex), (78 : Vertex), (85 : Vertex), (86 : Vertex), (89 : Vertex), (90 : Vertex), (95 : Vertex), (192 : Vertex), (195 : Vertex), (207 : Vertex), (210 : Vertex), (212 : Vertex), (219 : Vertex), (221 : Vertex), (258 : Vertex), (260 : Vertex), (264 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (275 : Vertex), (277 : Vertex), (281 : Vertex), (287 : Vertex), (323 : Vertex), (325 : Vertex), (332 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (340 : Vertex), (344 : Vertex), (347 : Vertex), (350 : Vertex), (384 : Vertex), (387 : Vertex), (396 : Vertex), (399 : Vertex), (402 : Vertex), (404 : Vertex), (408 : Vertex), (413 : Vertex), (452 : Vertex), (455 : Vertex), (456 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (469 : Vertex), (473 : Vertex), (474 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (7 : Vertex), (8 : Vertex), (13 : Vertex), (14 : Vertex), (15 : Vertex), (18 : Vertex), (19 : Vertex), (20 : Vertex), (22 : Vertex), (26 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (64 : Vertex), (65 : Vertex), (66 : Vertex), (68 : Vertex), (69 : Vertex), (70 : Vertex), (72 : Vertex), (73 : Vertex), (74 : Vertex), (75 : Vertex), (78 : Vertex), (81 : Vertex), (82 : Vertex), (84 : Vertex), (85 : Vertex), (86 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (90 : Vertex), (91 : Vertex), (93 : Vertex), (95 : Vertex), (192 : Vertex), (193 : Vertex), (195 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (207 : Vertex), (210 : Vertex), (211 : Vertex), (212 : Vertex), (214 : Vertex), (218 : Vertex), (219 : Vertex), (220 : Vertex), (221 : Vertex), (258 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (273 : Vertex), (275 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (285 : Vertex), (287 : Vertex), (321 : Vertex), (322 : Vertex), (323 : Vertex), (325 : Vertex), (327 : Vertex), (328 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (338 : Vertex), (340 : Vertex), (342 : Vertex), (344 : Vertex), (346 : Vertex), (347 : Vertex), (348 : Vertex), (350 : Vertex), (351 : Vertex), (384 : Vertex), (385 : Vertex), (387 : Vertex), (391 : Vertex), (397 : Vertex), (399 : Vertex), (400 : Vertex), (402 : Vertex), (403 : Vertex), (404 : Vertex), (408 : Vertex), (413 : Vertex), (448 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex)]
def head : Vertex := 396
def ban : Nat := 13407807929361398538564566754911466725583239419581805114146830010759410637152977216616052573033417674868174893095019636958445069862753924792986614485950068
def reachable : Nat := 581198561009458243294379401896126401010588263576731432962353392920569760185821725133485752821856965091466413895308812949192645153447034520134027
theorem ban_eq : banFrom (fun i => pre[i]!) 111 = ban := by decide
theorem head_eq : pre[111]! = head.val := by decide
theorem region_closed : expand reachable &&& freeOf ban = reachable := by decide
theorem region_start : ∀ y : Fin 512,
    (expand (2^head.val) &&& freeOf ban).testBit y.val = true →
    reachable.testBit y.val = true := by decide
theorem region_mem : ∀ v : Vertex,
    v = head ∨ reachable.testBit v.val = true → v ∈ region := by decide
theorem odd_mem : ∀ v : Vertex, v ∈ region → bitParity v.val = true → v ∈ oddSide := by decide
theorem even_mem : ∀ v : Vertex, v ∈ region → bitParity v.val = false → v ∈ evenSide := by decide
theorem others_mem : ∀ v : Vertex, v ∈ region → v ≠ head → v ∈ others := by decide
theorem others_nodup : others.Nodup := by decide
theorem head_not_others : head ∉ others := by decide
theorem oddSide_length : oddSide.length = 61 := by decide
theorem evenSide_length : evenSide.length = 63 := by decide

theorem suffix_head (p : Snake 192) (hp : StartsWith p pre 112) :
    (suffix p).vertex 0 = head := by
  apply Fin.ext
  exact (hp 111 (by decide) (by decide)).trans head_eq

theorem suffix_covered (p : Snake 192) (hp : StartsWith p pre 112) :
    ∀ v, InPath (suffix p) v → v ∈ region := by
  have hb : banFrom (vals p) 111 = ban := by
    rw [← ban_eq]
    apply banFrom_congr
    intro i hi
    have hi' : i < 193 := by omega
    simpa only [vals, dif_pos hi'] using hp i (by omega) hi'
  have hh : vals p 111 = head.val := by
    exact congrArg Fin.val (suffix_head p hp)
  have hv := tail_valid p 81 111 (by decide)
  rw [hb,hh] at hv
  intro v hsel
  obtain ⟨i,rfl⟩ := hsel
  apply region_mem
  by_cases hi : i.val = 0
  · left
    have he : i = 0 := Fin.ext hi
    rw [he]
    exact suffix_head p hp
  · right
    apply hv.in_region region_closed region_start (Or.inl rfl) (fun _ h => h)
    apply List.mem_map.mpr
    refine ⟨i.val-1,List.mem_range.mpr (by omega),?_⟩
    have he : 111+1+(i.val-1) = 111+i.val := by omega
    simp only [he,vals,dif_pos (show 111+i.val < 193 by omega),suffix]

end Snake9.Regrowth.E112041
