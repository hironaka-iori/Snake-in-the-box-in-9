import RegrowthParityCounts
namespace Snake9.Regrowth.E112251
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[152, 153, 155, 159, 151, 149, 148, 132, 140, 142, 138, 130, 131, 387, 259, 258, 266, 270, 268, 260, 261, 277, 279, 287, 283, 281, 280, 272, 400, 432, 436, 437, 439, 447, 443, 427, 491, 495, 493, 485, 481, 497, 499, 498, 502, 510, 508, 504, 248, 249, 251, 255, 247, 245, 244, 228, 236, 238, 234, 226, 227, 99, 35, 34, 42, 46, 44, 36, 37, 53, 55, 63, 59, 57, 56, 48, 112, 80, 84, 85, 87, 95, 91, 75, 331, 335, 333, 349, 348, 350, 342, 338, 339, 337, 321, 320, 328, 72, 200, 192, 193, 209, 211, 210, 214, 222, 220, 221, 205, 207, 199, 455]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (7 : Vertex), (9 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (70 : Vertex), (78 : Vertex), (102 : Vertex), (105 : Vertex), (109 : Vertex), (111 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (173 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (354 : Vertex), (356 : Vertex), (358 : Vertex), (359 : Vertex), (361 : Vertex), (362 : Vertex), (364 : Vertex), (366 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (377 : Vertex), (378 : Vertex), (379 : Vertex), (383 : Vertex), (390 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (418 : Vertex), (422 : Vertex), (424 : Vertex), (428 : Vertex), (430 : Vertex), (450 : Vertex), (452 : Vertex), (454 : Vertex), (455 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (462 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (13 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (70 : Vertex), (109 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (161 : Vertex), (167 : Vertex), (168 : Vertex), (173 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (289 : Vertex), (295 : Vertex), (296 : Vertex), (301 : Vertex), (307 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (358 : Vertex), (361 : Vertex), (362 : Vertex), (364 : Vertex), (372 : Vertex), (375 : Vertex), (379 : Vertex), (392 : Vertex), (397 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (422 : Vertex), (428 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (468 : Vertex), (471 : Vertex), (475 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (9 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (78 : Vertex), (102 : Vertex), (105 : Vertex), (111 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (166 : Vertex), (169 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (189 : Vertex), (190 : Vertex), (288 : Vertex), (294 : Vertex), (297 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (317 : Vertex), (318 : Vertex), (354 : Vertex), (356 : Vertex), (359 : Vertex), (366 : Vertex), (373 : Vertex), (377 : Vertex), (378 : Vertex), (383 : Vertex), (390 : Vertex), (393 : Vertex), (399 : Vertex), (413 : Vertex), (414 : Vertex), (418 : Vertex), (424 : Vertex), (430 : Vertex), (450 : Vertex), (452 : Vertex), (455 : Vertex), (462 : Vertex), (469 : Vertex), (473 : Vertex), (474 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (7 : Vertex), (9 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (70 : Vertex), (78 : Vertex), (102 : Vertex), (105 : Vertex), (109 : Vertex), (111 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (173 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (354 : Vertex), (356 : Vertex), (358 : Vertex), (359 : Vertex), (361 : Vertex), (362 : Vertex), (364 : Vertex), (366 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (377 : Vertex), (378 : Vertex), (379 : Vertex), (383 : Vertex), (390 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (418 : Vertex), (422 : Vertex), (424 : Vertex), (428 : Vertex), (430 : Vertex), (450 : Vertex), (452 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (462 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (479 : Vertex)]
def head : Vertex := 455
def ban : Nat := 13407807928202602535370975710504980819209909421805650339834919938618328828634797588529331064146312068789830959233295192848629874480445795570693219164446012
def reachable : Nat := 1739994564203049287700865308269456398786743037888641505103435201438749388272543234020591358900200898953190858005124008331500774375740429841638083
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
theorem oddSide_length : oddSide.length = 49 := by decide
theorem evenSide_length : evenSide.length = 55 := by decide

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

end Snake9.Regrowth.E112251
