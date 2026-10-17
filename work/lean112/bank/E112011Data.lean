import RegrowthParityCounts
namespace Snake9.Regrowth.E112011
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[118, 119, 117, 113, 121, 123, 107, 106, 98, 96, 100, 108, 109, 45, 173, 172, 164, 160, 162, 170, 186, 187, 185, 177, 181, 183, 182, 438, 434, 432, 440, 444, 445, 447, 431, 427, 419, 417, 421, 485, 501, 497, 505, 507, 506, 490, 488, 232, 233, 225, 227, 243, 242, 240, 244, 252, 253, 255, 239, 238, 230, 486, 358, 366, 367, 383, 381, 380, 376, 368, 370, 371, 355, 353, 361, 297, 313, 315, 314, 298, 290, 288, 292, 308, 309, 311, 295, 39, 35, 51, 50, 48, 56, 60, 62, 30, 26, 27, 25, 17, 21, 5, 261, 257, 259, 267, 271, 287, 285, 284, 280, 272]
def region : List Vertex := [(0 : Vertex), (2 : Vertex), (6 : Vertex), (8 : Vertex), (12 : Vertex), (65 : Vertex), (67 : Vertex), (70 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (78 : Vertex), (79 : Vertex), (80 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (88 : Vertex), (92 : Vertex), (93 : Vertex), (95 : Vertex), (129 : Vertex), (131 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (139 : Vertex), (142 : Vertex), (143 : Vertex), (144 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (152 : Vertex), (156 : Vertex), (157 : Vertex), (159 : Vertex), (192 : Vertex), (194 : Vertex), (196 : Vertex), (197 : Vertex), (199 : Vertex), (202 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (209 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (216 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (222 : Vertex), (262 : Vertex), (272 : Vertex), (274 : Vertex), (278 : Vertex), (320 : Vertex), (322 : Vertex), (324 : Vertex), (327 : Vertex), (328 : Vertex), (330 : Vertex), (332 : Vertex), (333 : Vertex), (337 : Vertex), (340 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (350 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (401 : Vertex), (403 : Vertex), (404 : Vertex), (405 : Vertex), (407 : Vertex), (409 : Vertex), (410 : Vertex), (411 : Vertex), (414 : Vertex), (448 : Vertex), (449 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (455 : Vertex), (457 : Vertex), (459 : Vertex), (460 : Vertex), (461 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (470 : Vertex), (471 : Vertex), (472 : Vertex), (476 : Vertex), (477 : Vertex), (478 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(2 : Vertex), (8 : Vertex), (67 : Vertex), (70 : Vertex), (73 : Vertex), (79 : Vertex), (82 : Vertex), (84 : Vertex), (88 : Vertex), (93 : Vertex), (131 : Vertex), (134 : Vertex), (137 : Vertex), (143 : Vertex), (146 : Vertex), (148 : Vertex), (152 : Vertex), (157 : Vertex), (194 : Vertex), (196 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (262 : Vertex), (274 : Vertex), (322 : Vertex), (324 : Vertex), (327 : Vertex), (328 : Vertex), (333 : Vertex), (341 : Vertex), (342 : Vertex), (345 : Vertex), (346 : Vertex), (386 : Vertex), (388 : Vertex), (391 : Vertex), (392 : Vertex), (397 : Vertex), (398 : Vertex), (403 : Vertex), (405 : Vertex), (409 : Vertex), (410 : Vertex), (448 : Vertex), (451 : Vertex), (457 : Vertex), (460 : Vertex), (463 : Vertex), (466 : Vertex), (468 : Vertex), (471 : Vertex), (472 : Vertex), (477 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (12 : Vertex), (65 : Vertex), (71 : Vertex), (72 : Vertex), (78 : Vertex), (80 : Vertex), (83 : Vertex), (92 : Vertex), (95 : Vertex), (129 : Vertex), (135 : Vertex), (136 : Vertex), (139 : Vertex), (142 : Vertex), (144 : Vertex), (147 : Vertex), (156 : Vertex), (159 : Vertex), (192 : Vertex), (197 : Vertex), (202 : Vertex), (204 : Vertex), (209 : Vertex), (215 : Vertex), (216 : Vertex), (219 : Vertex), (222 : Vertex), (272 : Vertex), (278 : Vertex), (320 : Vertex), (330 : Vertex), (332 : Vertex), (337 : Vertex), (340 : Vertex), (343 : Vertex), (347 : Vertex), (350 : Vertex), (384 : Vertex), (390 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (401 : Vertex), (404 : Vertex), (407 : Vertex), (411 : Vertex), (414 : Vertex), (449 : Vertex), (450 : Vertex), (452 : Vertex), (455 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (470 : Vertex), (476 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (2 : Vertex), (6 : Vertex), (8 : Vertex), (12 : Vertex), (65 : Vertex), (67 : Vertex), (70 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (78 : Vertex), (79 : Vertex), (80 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (88 : Vertex), (92 : Vertex), (93 : Vertex), (95 : Vertex), (129 : Vertex), (131 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (139 : Vertex), (142 : Vertex), (143 : Vertex), (144 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (152 : Vertex), (156 : Vertex), (157 : Vertex), (159 : Vertex), (192 : Vertex), (194 : Vertex), (196 : Vertex), (197 : Vertex), (199 : Vertex), (202 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (209 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (216 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (222 : Vertex), (262 : Vertex), (274 : Vertex), (278 : Vertex), (320 : Vertex), (322 : Vertex), (324 : Vertex), (327 : Vertex), (328 : Vertex), (330 : Vertex), (332 : Vertex), (333 : Vertex), (337 : Vertex), (340 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (350 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (401 : Vertex), (403 : Vertex), (404 : Vertex), (405 : Vertex), (407 : Vertex), (409 : Vertex), (410 : Vertex), (411 : Vertex), (414 : Vertex), (448 : Vertex), (449 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (455 : Vertex), (457 : Vertex), (459 : Vertex), (460 : Vertex), (461 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (470 : Vertex), (471 : Vertex), (472 : Vertex), (476 : Vertex), (477 : Vertex), (478 : Vertex), (479 : Vertex)]
def head : Vertex := 272
def ban : Nat := 13407807926993189733449966801344661786323596557475027812163551343618272813005438385863105117495883853677274729227295266013921147550510232832044546989747898
def reachable : Nat := 2949407366124058196861184341155769263117365565560010100103491217068108590938769180671019574012757128959190784839832735261436337114389102016336197
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
theorem evenSide_length : evenSide.length = 61 := by decide

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

end Snake9.Regrowth.E112011
