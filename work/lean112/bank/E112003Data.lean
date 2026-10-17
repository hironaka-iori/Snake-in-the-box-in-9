import RegrowthParityCounts
namespace Snake9.Regrowth.E112003
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[56, 57, 59, 63, 55, 53, 52, 36, 44, 46, 42, 34, 35, 99, 227, 226, 234, 238, 236, 228, 244, 245, 247, 255, 251, 249, 248, 504, 508, 510, 502, 498, 499, 497, 481, 485, 493, 495, 491, 427, 443, 447, 439, 437, 436, 420, 422, 166, 167, 175, 173, 189, 188, 190, 186, 178, 179, 177, 161, 160, 168, 424, 296, 288, 289, 305, 307, 306, 310, 318, 316, 317, 301, 303, 295, 359, 375, 373, 372, 356, 364, 366, 362, 378, 379, 377, 361, 105, 109, 125, 124, 126, 118, 114, 112, 80, 84, 85, 87, 95, 91, 75, 331, 335, 333, 325, 321, 337, 339, 338, 342, 350]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (5 : Vertex), (6 : Vertex), (7 : Vertex), (8 : Vertex), (9 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (70 : Vertex), (72 : Vertex), (76 : Vertex), (78 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (197 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (287 : Vertex), (328 : Vertex), (344 : Vertex), (348 : Vertex), (350 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (391 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (448 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (8 : Vertex), (13 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (70 : Vertex), (76 : Vertex), (131 : Vertex), (133 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (155 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (259 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (276 : Vertex), (279 : Vertex), (280 : Vertex), (283 : Vertex), (328 : Vertex), (348 : Vertex), (385 : Vertex), (386 : Vertex), (391 : Vertex), (397 : Vertex), (398 : Vertex), (400 : Vertex), (403 : Vertex), (406 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (448 : Vertex), (451 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (468 : Vertex), (471 : Vertex), (475 : Vertex), (477 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (5 : Vertex), (6 : Vertex), (9 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (72 : Vertex), (78 : Vertex), (130 : Vertex), (132 : Vertex), (139 : Vertex), (142 : Vertex), (144 : Vertex), (149 : Vertex), (150 : Vertex), (153 : Vertex), (159 : Vertex), (192 : Vertex), (197 : Vertex), (198 : Vertex), (201 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (260 : Vertex), (270 : Vertex), (272 : Vertex), (277 : Vertex), (281 : Vertex), (282 : Vertex), (287 : Vertex), (344 : Vertex), (350 : Vertex), (384 : Vertex), (387 : Vertex), (389 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (408 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (452 : Vertex), (455 : Vertex), (456 : Vertex), (462 : Vertex), (464 : Vertex), (469 : Vertex), (473 : Vertex), (474 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (5 : Vertex), (6 : Vertex), (7 : Vertex), (8 : Vertex), (9 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (70 : Vertex), (72 : Vertex), (76 : Vertex), (78 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (197 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (287 : Vertex), (328 : Vertex), (344 : Vertex), (348 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (391 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (448 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex), (479 : Vertex)]
def head : Vertex := 350
def ban : Nat := 13407807927812336046831226117181315322253357071771753333637124803466185940840005662232926375480485574395638962169389729062533928443839935907519480200256540
def reachable : Nat := 2130261052742798881024530805226008748820640044086436640255578089233541314568947922686417853294392896017096321791219954368106634038914168805827555
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
theorem oddSide_length : oddSide.length = 59 := by decide
theorem evenSide_length : evenSide.length = 62 := by decide

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

end Snake9.Regrowth.E112003
