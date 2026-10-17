import RegrowthParityCounts
namespace Snake9.Regrowth.E112219
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[56, 57, 59, 63, 55, 53, 37, 36, 44, 46, 42, 34, 35, 99, 227, 226, 234, 238, 236, 228, 244, 245, 247, 255, 251, 249, 248, 504, 508, 510, 502, 498, 499, 497, 481, 485, 493, 495, 491, 427, 443, 447, 439, 437, 436, 432, 400, 144, 152, 153, 155, 159, 151, 149, 133, 132, 140, 142, 138, 130, 131, 387, 259, 258, 266, 270, 268, 260, 276, 277, 279, 287, 283, 281, 280, 344, 348, 350, 342, 338, 339, 337, 321, 325, 333, 335, 331, 75, 91, 95, 87, 85, 84, 80, 112, 114, 118, 126, 124, 125, 109, 105, 361, 377, 379, 378, 362, 366, 364, 356, 372, 373]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (7 : Vertex), (8 : Vertex), (9 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (70 : Vertex), (72 : Vertex), (76 : Vertex), (78 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (173 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (359 : Vertex), (373 : Vertex), (375 : Vertex), (390 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (418 : Vertex), (422 : Vertex), (424 : Vertex), (428 : Vertex), (430 : Vertex), (448 : Vertex), (450 : Vertex), (452 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (462 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (8 : Vertex), (13 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (70 : Vertex), (76 : Vertex), (161 : Vertex), (167 : Vertex), (168 : Vertex), (173 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (289 : Vertex), (295 : Vertex), (296 : Vertex), (301 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (375 : Vertex), (392 : Vertex), (397 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (422 : Vertex), (428 : Vertex), (448 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (468 : Vertex), (471 : Vertex), (475 : Vertex), (477 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (9 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (72 : Vertex), (78 : Vertex), (160 : Vertex), (166 : Vertex), (169 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (189 : Vertex), (190 : Vertex), (192 : Vertex), (198 : Vertex), (201 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (221 : Vertex), (222 : Vertex), (288 : Vertex), (294 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (317 : Vertex), (318 : Vertex), (359 : Vertex), (373 : Vertex), (390 : Vertex), (393 : Vertex), (399 : Vertex), (413 : Vertex), (414 : Vertex), (418 : Vertex), (424 : Vertex), (430 : Vertex), (450 : Vertex), (452 : Vertex), (455 : Vertex), (456 : Vertex), (462 : Vertex), (469 : Vertex), (473 : Vertex), (474 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (7 : Vertex), (8 : Vertex), (9 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (70 : Vertex), (72 : Vertex), (76 : Vertex), (78 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (173 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (359 : Vertex), (375 : Vertex), (390 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (418 : Vertex), (422 : Vertex), (424 : Vertex), (428 : Vertex), (430 : Vertex), (448 : Vertex), (450 : Vertex), (452 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (462 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex), (479 : Vertex)]
def head : Vertex := 373
def ban : Nat := 13407807927812383686748567827773628304017982458653927186922995017585235664430130746308529130058959064855123850155328741859578665492645540310084088736341052
def reachable : Nat := 2130213412825457170432217823461383361938466190800566426136528365643416230493345168107944362834908008031157308994175217319301029636349560269743043
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
theorem oddSide_length : oddSide.length = 50 := by decide
theorem evenSide_length : evenSide.length = 53 := by decide

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

end Snake9.Regrowth.E112219
