import RegrowthParityCounts
namespace Snake9.Regrowth.E112015
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[118, 119, 103, 101, 100, 108, 104, 106, 107, 123, 121, 113, 112, 48, 56, 58, 62, 190, 182, 183, 167, 165, 164, 160, 168, 170, 171, 187, 185, 177, 433, 417, 419, 418, 434, 442, 440, 444, 428, 429, 431, 447, 511, 507, 491, 490, 488, 480, 484, 486, 230, 238, 239, 237, 233, 225, 227, 243, 242, 250, 248, 252, 244, 245, 501, 373, 372, 380, 376, 378, 370, 354, 355, 353, 361, 365, 367, 366, 302, 298, 296, 288, 292, 293, 295, 311, 307, 315, 313, 317, 61, 45, 41, 33, 35, 34, 38, 6, 70, 78, 79, 77, 73, 65, 67, 83, 82, 90, 88, 92, 84, 85]
def region : List Vertex := [(0 : Vertex), (5 : Vertex), (8 : Vertex), (10 : Vertex), (11 : Vertex), (12 : Vertex), (17 : Vertex), (21 : Vertex), (23 : Vertex), (25 : Vertex), (27 : Vertex), (31 : Vertex), (85 : Vertex), (129 : Vertex), (130 : Vertex), (131 : Vertex), (137 : Vertex), (140 : Vertex), (141 : Vertex), (142 : Vertex), (143 : Vertex), (144 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (152 : Vertex), (154 : Vertex), (156 : Vertex), (157 : Vertex), (159 : Vertex), (192 : Vertex), (194 : Vertex), (196 : Vertex), (197 : Vertex), (199 : Vertex), (200 : Vertex), (202 : Vertex), (203 : Vertex), (204 : Vertex), (208 : Vertex), (209 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (219 : Vertex), (221 : Vertex), (222 : Vertex), (223 : Vertex), (257 : Vertex), (258 : Vertex), (259 : Vertex), (265 : Vertex), (267 : Vertex), (268 : Vertex), (269 : Vertex), (271 : Vertex), (272 : Vertex), (273 : Vertex), (274 : Vertex), (276 : Vertex), (277 : Vertex), (278 : Vertex), (280 : Vertex), (282 : Vertex), (284 : Vertex), (286 : Vertex), (287 : Vertex), (320 : Vertex), (324 : Vertex), (325 : Vertex), (327 : Vertex), (328 : Vertex), (330 : Vertex), (331 : Vertex), (332 : Vertex), (336 : Vertex), (337 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (347 : Vertex), (349 : Vertex), (350 : Vertex), (351 : Vertex), (384 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (394 : Vertex), (395 : Vertex), (398 : Vertex), (400 : Vertex), (403 : Vertex), (404 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (409 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex), (449 : Vertex), (450 : Vertex), (451 : Vertex), (453 : Vertex), (455 : Vertex), (457 : Vertex), (460 : Vertex), (461 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (465 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (470 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (474 : Vertex), (476 : Vertex), (477 : Vertex), (478 : Vertex)]
def oddSide : List Vertex := [(8 : Vertex), (11 : Vertex), (21 : Vertex), (25 : Vertex), (31 : Vertex), (131 : Vertex), (137 : Vertex), (140 : Vertex), (143 : Vertex), (146 : Vertex), (148 : Vertex), (152 : Vertex), (157 : Vertex), (194 : Vertex), (196 : Vertex), (199 : Vertex), (200 : Vertex), (203 : Vertex), (208 : Vertex), (214 : Vertex), (217 : Vertex), (223 : Vertex), (259 : Vertex), (265 : Vertex), (268 : Vertex), (271 : Vertex), (273 : Vertex), (274 : Vertex), (276 : Vertex), (280 : Vertex), (286 : Vertex), (324 : Vertex), (327 : Vertex), (328 : Vertex), (331 : Vertex), (336 : Vertex), (342 : Vertex), (345 : Vertex), (351 : Vertex), (388 : Vertex), (391 : Vertex), (392 : Vertex), (395 : Vertex), (398 : Vertex), (400 : Vertex), (403 : Vertex), (405 : Vertex), (406 : Vertex), (409 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex), (460 : Vertex), (463 : Vertex), (465 : Vertex), (466 : Vertex), (468 : Vertex), (471 : Vertex), (472 : Vertex), (477 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (5 : Vertex), (10 : Vertex), (12 : Vertex), (17 : Vertex), (23 : Vertex), (27 : Vertex), (85 : Vertex), (129 : Vertex), (130 : Vertex), (141 : Vertex), (142 : Vertex), (144 : Vertex), (147 : Vertex), (149 : Vertex), (154 : Vertex), (156 : Vertex), (159 : Vertex), (192 : Vertex), (197 : Vertex), (202 : Vertex), (204 : Vertex), (209 : Vertex), (215 : Vertex), (219 : Vertex), (221 : Vertex), (222 : Vertex), (257 : Vertex), (258 : Vertex), (267 : Vertex), (269 : Vertex), (272 : Vertex), (277 : Vertex), (278 : Vertex), (282 : Vertex), (284 : Vertex), (287 : Vertex), (320 : Vertex), (325 : Vertex), (330 : Vertex), (332 : Vertex), (337 : Vertex), (343 : Vertex), (347 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (389 : Vertex), (390 : Vertex), (393 : Vertex), (394 : Vertex), (404 : Vertex), (407 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex), (449 : Vertex), (450 : Vertex), (455 : Vertex), (461 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (470 : Vertex), (473 : Vertex), (474 : Vertex), (476 : Vertex)]
def others : List Vertex := [(0 : Vertex), (5 : Vertex), (8 : Vertex), (10 : Vertex), (11 : Vertex), (12 : Vertex), (17 : Vertex), (21 : Vertex), (23 : Vertex), (25 : Vertex), (27 : Vertex), (31 : Vertex), (129 : Vertex), (130 : Vertex), (131 : Vertex), (137 : Vertex), (140 : Vertex), (141 : Vertex), (142 : Vertex), (143 : Vertex), (144 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (152 : Vertex), (154 : Vertex), (156 : Vertex), (157 : Vertex), (159 : Vertex), (192 : Vertex), (194 : Vertex), (196 : Vertex), (197 : Vertex), (199 : Vertex), (200 : Vertex), (202 : Vertex), (203 : Vertex), (204 : Vertex), (208 : Vertex), (209 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (219 : Vertex), (221 : Vertex), (222 : Vertex), (223 : Vertex), (257 : Vertex), (258 : Vertex), (259 : Vertex), (265 : Vertex), (267 : Vertex), (268 : Vertex), (269 : Vertex), (271 : Vertex), (272 : Vertex), (273 : Vertex), (274 : Vertex), (276 : Vertex), (277 : Vertex), (278 : Vertex), (280 : Vertex), (282 : Vertex), (284 : Vertex), (286 : Vertex), (287 : Vertex), (320 : Vertex), (324 : Vertex), (325 : Vertex), (327 : Vertex), (328 : Vertex), (330 : Vertex), (331 : Vertex), (332 : Vertex), (336 : Vertex), (337 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (347 : Vertex), (349 : Vertex), (350 : Vertex), (351 : Vertex), (384 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (394 : Vertex), (395 : Vertex), (398 : Vertex), (400 : Vertex), (403 : Vertex), (404 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (409 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex), (449 : Vertex), (450 : Vertex), (451 : Vertex), (453 : Vertex), (455 : Vertex), (457 : Vertex), (460 : Vertex), (461 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (465 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (470 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (474 : Vertex), (476 : Vertex), (477 : Vertex), (478 : Vertex)]
def head : Vertex := 85
def ban : Nat := 13407807928480804236417787468276232775456897156404271608697989710349904232733915967174252114700341403830337041288901642231242586586948588927938518241370846
def reachable : Nat := 1461792863156237529929613352022468664188121769025571733371859797339631009627622183466562023859694816897584408622511296224997981018495130764713249
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
theorem evenSide_length : evenSide.length = 67 := by decide

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

end Snake9.Regrowth.E112015
