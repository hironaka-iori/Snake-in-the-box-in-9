import RegrowthParityCounts
namespace Snake9.Regrowth.E112052
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 8, 10, 26, 27, 25, 29, 21, 20, 22, 6, 7, 15, 79, 75, 73, 65, 97, 113, 121, 123, 122, 106, 110, 366, 382, 380, 381, 365, 361, 363, 355, 371, 370, 368, 352, 288, 296, 298, 314, 315, 313, 305, 309, 308, 310, 294, 295, 303, 431, 175, 167, 166, 182, 180, 181, 189, 185, 187, 186, 170, 168, 160, 161, 417, 419, 435, 434, 432, 440, 444, 428, 492, 488, 490, 482, 486, 502, 500, 501, 497, 505, 507, 511, 255, 254, 252, 248, 240, 242, 243, 227, 235, 233, 237, 229, 228, 100, 36, 37, 45, 41, 43, 35, 34, 50, 48, 56, 60, 62, 63, 55]
def region : List Vertex := [(55 : Vertex), (66 : Vertex), (76 : Vertex), (80 : Vertex), (82 : Vertex), (83 : Vertex), (87 : Vertex), (88 : Vertex), (92 : Vertex), (94 : Vertex), (103 : Vertex), (118 : Vertex), (119 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (137 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (142 : Vertex), (144 : Vertex), (145 : Vertex), (146 : Vertex), (147 : Vertex), (151 : Vertex), (152 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (192 : Vertex), (194 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (202 : Vertex), (204 : Vertex), (206 : Vertex), (209 : Vertex), (212 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (257 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (265 : Vertex), (267 : Vertex), (268 : Vertex), (269 : Vertex), (270 : Vertex), (272 : Vertex), (274 : Vertex), (275 : Vertex), (279 : Vertex), (280 : Vertex), (284 : Vertex), (286 : Vertex), (287 : Vertex), (322 : Vertex), (324 : Vertex), (325 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (330 : Vertex), (332 : Vertex), (337 : Vertex), (340 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (351 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (394 : Vertex), (395 : Vertex), (397 : Vertex), (398 : Vertex), (401 : Vertex), (404 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (409 : Vertex), (410 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex), (415 : Vertex), (448 : Vertex), (449 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (455 : Vertex), (457 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (466 : Vertex), (467 : Vertex), (471 : Vertex), (472 : Vertex), (474 : Vertex), (476 : Vertex), (477 : Vertex), (478 : Vertex)]
def oddSide : List Vertex := [(55 : Vertex), (76 : Vertex), (82 : Vertex), (87 : Vertex), (88 : Vertex), (94 : Vertex), (103 : Vertex), (118 : Vertex), (131 : Vertex), (133 : Vertex), (137 : Vertex), (140 : Vertex), (145 : Vertex), (146 : Vertex), (151 : Vertex), (152 : Vertex), (158 : Vertex), (194 : Vertex), (199 : Vertex), (200 : Vertex), (206 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (259 : Vertex), (261 : Vertex), (265 : Vertex), (268 : Vertex), (274 : Vertex), (279 : Vertex), (280 : Vertex), (286 : Vertex), (322 : Vertex), (324 : Vertex), (327 : Vertex), (328 : Vertex), (341 : Vertex), (342 : Vertex), (345 : Vertex), (346 : Vertex), (351 : Vertex), (386 : Vertex), (388 : Vertex), (391 : Vertex), (392 : Vertex), (395 : Vertex), (397 : Vertex), (398 : Vertex), (405 : Vertex), (406 : Vertex), (409 : Vertex), (410 : Vertex), (415 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex), (463 : Vertex), (466 : Vertex), (471 : Vertex), (472 : Vertex), (477 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(66 : Vertex), (80 : Vertex), (83 : Vertex), (92 : Vertex), (119 : Vertex), (130 : Vertex), (132 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex), (144 : Vertex), (147 : Vertex), (156 : Vertex), (159 : Vertex), (192 : Vertex), (198 : Vertex), (202 : Vertex), (204 : Vertex), (209 : Vertex), (212 : Vertex), (215 : Vertex), (219 : Vertex), (221 : Vertex), (257 : Vertex), (258 : Vertex), (260 : Vertex), (267 : Vertex), (269 : Vertex), (270 : Vertex), (272 : Vertex), (275 : Vertex), (284 : Vertex), (287 : Vertex), (325 : Vertex), (326 : Vertex), (330 : Vertex), (332 : Vertex), (337 : Vertex), (340 : Vertex), (343 : Vertex), (344 : Vertex), (347 : Vertex), (384 : Vertex), (389 : Vertex), (390 : Vertex), (393 : Vertex), (394 : Vertex), (401 : Vertex), (404 : Vertex), (407 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (474 : Vertex), (476 : Vertex)]
def others : List Vertex := [(66 : Vertex), (76 : Vertex), (80 : Vertex), (82 : Vertex), (83 : Vertex), (87 : Vertex), (88 : Vertex), (92 : Vertex), (94 : Vertex), (103 : Vertex), (118 : Vertex), (119 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (137 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (142 : Vertex), (144 : Vertex), (145 : Vertex), (146 : Vertex), (147 : Vertex), (151 : Vertex), (152 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (192 : Vertex), (194 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (202 : Vertex), (204 : Vertex), (206 : Vertex), (209 : Vertex), (212 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (257 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (265 : Vertex), (267 : Vertex), (268 : Vertex), (269 : Vertex), (270 : Vertex), (272 : Vertex), (274 : Vertex), (275 : Vertex), (279 : Vertex), (280 : Vertex), (284 : Vertex), (286 : Vertex), (287 : Vertex), (322 : Vertex), (324 : Vertex), (325 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (330 : Vertex), (332 : Vertex), (337 : Vertex), (340 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (351 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (394 : Vertex), (395 : Vertex), (397 : Vertex), (398 : Vertex), (401 : Vertex), (404 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (409 : Vertex), (410 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex), (415 : Vertex), (448 : Vertex), (449 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (455 : Vertex), (457 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (466 : Vertex), (467 : Vertex), (471 : Vertex), (472 : Vertex), (474 : Vertex), (476 : Vertex), (477 : Vertex), (478 : Vertex)]
def head : Vertex := 55
def ban : Nat := 13407807928509100372500040924297363456394643685653136401305963767261675649805520366266853364474396019381288841701841445848873570792231835784256828752265215
def reachable : Nat := 1433496727073984073908482671084722134939256976417597676460088380268026610535020933692507408308743016484644605004880312019714734162176820253818880
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
theorem oddSide_length : oddSide.length = 64 := by decide
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

end Snake9.Regrowth.E112052
