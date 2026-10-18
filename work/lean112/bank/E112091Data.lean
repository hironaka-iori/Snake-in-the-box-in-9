import RegrowthParityCounts
namespace Snake9.Regrowth.E112091
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[274, 272, 276, 284, 286, 287, 271, 269, 333, 332, 324, 326, 342, 343, 341, 337, 345, 344, 346, 330, 331, 323, 259, 387, 395, 394, 410, 408, 409, 413, 405, 407, 406, 390, 388, 396, 140, 156, 158, 159, 143, 135, 133, 129, 145, 144, 146, 130, 194, 198, 214, 215, 213, 221, 205, 237, 493, 492, 484, 486, 502, 503, 501, 497, 505, 504, 506, 490, 491, 483, 227, 99, 107, 106, 122, 120, 121, 125, 117, 119, 118, 102, 100, 108, 44, 60, 62, 63, 47, 39, 37, 33, 49, 48, 50, 34, 290, 294, 310, 311, 309, 317, 313, 315, 379, 371, 370, 368, 372, 380, 382, 366]
def region : List Vertex := [(0 : Vertex), (4 : Vertex), (6 : Vertex), (8 : Vertex), (9 : Vertex), (10 : Vertex), (11 : Vertex), (14 : Vertex), (19 : Vertex), (21 : Vertex), (22 : Vertex), (23 : Vertex), (24 : Vertex), (25 : Vertex), (26 : Vertex), (27 : Vertex), (29 : Vertex), (64 : Vertex), (65 : Vertex), (69 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (78 : Vertex), (79 : Vertex), (80 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (91 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (160 : Vertex), (164 : Vertex), (166 : Vertex), (168 : Vertex), (169 : Vertex), (170 : Vertex), (171 : Vertex), (174 : Vertex), (179 : Vertex), (180 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (200 : Vertex), (203 : Vertex), (216 : Vertex), (218 : Vertex), (219 : Vertex), (224 : Vertex), (232 : Vertex), (238 : Vertex), (240 : Vertex), (242 : Vertex), (244 : Vertex), (251 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (264 : Vertex), (296 : Vertex), (353 : Vertex), (357 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (366 : Vertex), (367 : Vertex), (416 : Vertex), (417 : Vertex), (421 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (430 : Vertex), (431 : Vertex), (432 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (444 : Vertex), (446 : Vertex), (447 : Vertex), (448 : Vertex), (449 : Vertex), (453 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (475 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(4 : Vertex), (8 : Vertex), (11 : Vertex), (14 : Vertex), (19 : Vertex), (21 : Vertex), (22 : Vertex), (25 : Vertex), (26 : Vertex), (64 : Vertex), (69 : Vertex), (73 : Vertex), (79 : Vertex), (82 : Vertex), (84 : Vertex), (91 : Vertex), (94 : Vertex), (164 : Vertex), (168 : Vertex), (171 : Vertex), (174 : Vertex), (179 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (200 : Vertex), (203 : Vertex), (218 : Vertex), (224 : Vertex), (242 : Vertex), (244 : Vertex), (251 : Vertex), (254 : Vertex), (296 : Vertex), (357 : Vertex), (361 : Vertex), (367 : Vertex), (416 : Vertex), (421 : Vertex), (425 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (446 : Vertex), (448 : Vertex), (453 : Vertex), (457 : Vertex), (463 : Vertex), (466 : Vertex), (468 : Vertex), (475 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (9 : Vertex), (10 : Vertex), (23 : Vertex), (24 : Vertex), (27 : Vertex), (29 : Vertex), (65 : Vertex), (71 : Vertex), (72 : Vertex), (78 : Vertex), (80 : Vertex), (83 : Vertex), (92 : Vertex), (95 : Vertex), (160 : Vertex), (166 : Vertex), (169 : Vertex), (170 : Vertex), (180 : Vertex), (183 : Vertex), (184 : Vertex), (187 : Vertex), (189 : Vertex), (216 : Vertex), (219 : Vertex), (232 : Vertex), (238 : Vertex), (240 : Vertex), (252 : Vertex), (255 : Vertex), (264 : Vertex), (353 : Vertex), (359 : Vertex), (360 : Vertex), (366 : Vertex), (417 : Vertex), (423 : Vertex), (424 : Vertex), (430 : Vertex), (432 : Vertex), (435 : Vertex), (444 : Vertex), (447 : Vertex), (449 : Vertex), (455 : Vertex), (456 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (476 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (4 : Vertex), (6 : Vertex), (8 : Vertex), (9 : Vertex), (10 : Vertex), (11 : Vertex), (14 : Vertex), (19 : Vertex), (21 : Vertex), (22 : Vertex), (23 : Vertex), (24 : Vertex), (25 : Vertex), (26 : Vertex), (27 : Vertex), (29 : Vertex), (64 : Vertex), (65 : Vertex), (69 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (78 : Vertex), (79 : Vertex), (80 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (91 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (160 : Vertex), (164 : Vertex), (166 : Vertex), (168 : Vertex), (169 : Vertex), (170 : Vertex), (171 : Vertex), (174 : Vertex), (179 : Vertex), (180 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (200 : Vertex), (203 : Vertex), (216 : Vertex), (218 : Vertex), (219 : Vertex), (224 : Vertex), (232 : Vertex), (238 : Vertex), (240 : Vertex), (242 : Vertex), (244 : Vertex), (251 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (264 : Vertex), (296 : Vertex), (353 : Vertex), (357 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (367 : Vertex), (416 : Vertex), (417 : Vertex), (421 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (430 : Vertex), (431 : Vertex), (432 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (444 : Vertex), (446 : Vertex), (447 : Vertex), (448 : Vertex), (449 : Vertex), (453 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (475 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex)]
def head : Vertex := 366
def ban : Nat := 13407807927307203968413763417458315555857666781350312041508238330732218609771248869754781442117629608892677464312987566459852475636971308124389457949864110
def reachable : Nat := 2635393131160261580747530571621699039242081336215323112989545420302298107047092856049273818797354393873498484393901407174975261822044191056219985
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
theorem oddSide_length : oddSide.length = 53 := by decide
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

end Snake9.Regrowth.E112091
