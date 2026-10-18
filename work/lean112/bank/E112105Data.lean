import RegrowthParityCounts
namespace Snake9.Regrowth.E112105
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[268, 269, 285, 287, 286, 278, 274, 272, 273, 257, 259, 267, 266, 10, 42, 58, 50, 48, 49, 33, 37, 101, 117, 119, 118, 102, 98, 96, 104, 120, 121, 123, 107, 363, 355, 353, 369, 368, 370, 378, 382, 383, 381, 365, 364, 356, 484, 420, 428, 429, 445, 447, 446, 438, 434, 432, 433, 417, 419, 427, 426, 490, 488, 504, 505, 507, 499, 503, 487, 231, 227, 225, 233, 237, 253, 255, 254, 250, 242, 240, 244, 180, 181, 183, 179, 187, 185, 184, 168, 160, 162, 166, 174, 175, 47, 303, 302, 294, 290, 288, 296, 297, 313, 315, 307, 311, 309, 308, 316, 60, 28, 24]
def region : List Vertex := [(0 : Vertex), (4 : Vertex), (6 : Vertex), (7 : Vertex), (9 : Vertex), (19 : Vertex), (21 : Vertex), (23 : Vertex), (24 : Vertex), (25 : Vertex), (27 : Vertex), (65 : Vertex), (67 : Vertex), (68 : Vertex), (71 : Vertex), (73 : Vertex), (76 : Vertex), (77 : Vertex), (78 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (90 : Vertex), (93 : Vertex), (94 : Vertex), (95 : Vertex), (129 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (135 : Vertex), (137 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (144 : Vertex), (145 : Vertex), (146 : Vertex), (150 : Vertex), (154 : Vertex), (157 : Vertex), (158 : Vertex), (159 : Vertex), (192 : Vertex), (194 : Vertex), (196 : Vertex), (197 : Vertex), (198 : Vertex), (200 : Vertex), (202 : Vertex), (203 : Vertex), (204 : Vertex), (206 : Vertex), (207 : Vertex), (209 : Vertex), (211 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (216 : Vertex), (217 : Vertex), (219 : Vertex), (220 : Vertex), (320 : Vertex), (322 : Vertex), (325 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (334 : Vertex), (335 : Vertex), (339 : Vertex), (340 : Vertex), (341 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (347 : Vertex), (348 : Vertex), (384 : Vertex), (386 : Vertex), (389 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (398 : Vertex), (399 : Vertex), (403 : Vertex), (404 : Vertex), (405 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (411 : Vertex), (412 : Vertex), (448 : Vertex), (449 : Vertex), (450 : Vertex), (451 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (459 : Vertex), (460 : Vertex), (461 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (465 : Vertex), (466 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (474 : Vertex), (476 : Vertex), (477 : Vertex), (478 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(4 : Vertex), (7 : Vertex), (19 : Vertex), (21 : Vertex), (25 : Vertex), (67 : Vertex), (73 : Vertex), (76 : Vertex), (79 : Vertex), (81 : Vertex), (82 : Vertex), (84 : Vertex), (93 : Vertex), (94 : Vertex), (131 : Vertex), (133 : Vertex), (137 : Vertex), (140 : Vertex), (145 : Vertex), (146 : Vertex), (157 : Vertex), (158 : Vertex), (194 : Vertex), (196 : Vertex), (200 : Vertex), (203 : Vertex), (206 : Vertex), (211 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (220 : Vertex), (322 : Vertex), (327 : Vertex), (328 : Vertex), (334 : Vertex), (339 : Vertex), (341 : Vertex), (345 : Vertex), (348 : Vertex), (386 : Vertex), (391 : Vertex), (392 : Vertex), (398 : Vertex), (403 : Vertex), (405 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (460 : Vertex), (463 : Vertex), (465 : Vertex), (466 : Vertex), (468 : Vertex), (477 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (9 : Vertex), (23 : Vertex), (24 : Vertex), (27 : Vertex), (65 : Vertex), (68 : Vertex), (71 : Vertex), (77 : Vertex), (78 : Vertex), (80 : Vertex), (83 : Vertex), (90 : Vertex), (95 : Vertex), (129 : Vertex), (132 : Vertex), (135 : Vertex), (139 : Vertex), (141 : Vertex), (144 : Vertex), (150 : Vertex), (154 : Vertex), (159 : Vertex), (192 : Vertex), (197 : Vertex), (198 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (209 : Vertex), (215 : Vertex), (216 : Vertex), (219 : Vertex), (320 : Vertex), (325 : Vertex), (326 : Vertex), (329 : Vertex), (335 : Vertex), (340 : Vertex), (343 : Vertex), (344 : Vertex), (347 : Vertex), (384 : Vertex), (389 : Vertex), (390 : Vertex), (393 : Vertex), (399 : Vertex), (404 : Vertex), (407 : Vertex), (408 : Vertex), (411 : Vertex), (449 : Vertex), (450 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex), (464 : Vertex), (469 : Vertex), (470 : Vertex), (474 : Vertex), (476 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (4 : Vertex), (6 : Vertex), (7 : Vertex), (9 : Vertex), (19 : Vertex), (21 : Vertex), (23 : Vertex), (25 : Vertex), (27 : Vertex), (65 : Vertex), (67 : Vertex), (68 : Vertex), (71 : Vertex), (73 : Vertex), (76 : Vertex), (77 : Vertex), (78 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (90 : Vertex), (93 : Vertex), (94 : Vertex), (95 : Vertex), (129 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (135 : Vertex), (137 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (144 : Vertex), (145 : Vertex), (146 : Vertex), (150 : Vertex), (154 : Vertex), (157 : Vertex), (158 : Vertex), (159 : Vertex), (192 : Vertex), (194 : Vertex), (196 : Vertex), (197 : Vertex), (198 : Vertex), (200 : Vertex), (202 : Vertex), (203 : Vertex), (204 : Vertex), (206 : Vertex), (207 : Vertex), (209 : Vertex), (211 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (216 : Vertex), (217 : Vertex), (219 : Vertex), (220 : Vertex), (320 : Vertex), (322 : Vertex), (325 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (334 : Vertex), (335 : Vertex), (339 : Vertex), (340 : Vertex), (341 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (347 : Vertex), (348 : Vertex), (384 : Vertex), (386 : Vertex), (389 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (398 : Vertex), (399 : Vertex), (403 : Vertex), (404 : Vertex), (405 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (411 : Vertex), (412 : Vertex), (448 : Vertex), (449 : Vertex), (450 : Vertex), (451 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (459 : Vertex), (460 : Vertex), (461 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (465 : Vertex), (466 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (474 : Vertex), (476 : Vertex), (477 : Vertex), (478 : Vertex), (479 : Vertex)]
def head : Vertex := 24
def ban : Nat := 13407807926961465455983024596707625597429056193276876683940253146732785155389934468253886005572516752265080595014519900335334716645598757826518313489399086
def reachable : Nat := 2981131643591000401498220530050309627315516693783308296988978874683612508547988292594386675424951263171966150518419166166347812119915335516685009
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

end Snake9.Regrowth.E112105
