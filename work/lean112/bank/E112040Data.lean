import RegrowthParityCounts
namespace Snake9.Regrowth.E112040
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 3, 7, 15, 13, 29, 28, 20, 22, 18, 26, 27, 91, 219, 218, 210, 214, 212, 220, 221, 205, 207, 199, 195, 193, 192, 200, 72, 74, 78, 70, 68, 69, 85, 81, 337, 321, 323, 322, 338, 342, 340, 348, 332, 333, 335, 351, 287, 279, 277, 261, 260, 262, 270, 266, 267, 265, 281, 280, 272, 400, 464, 472, 473, 457, 459, 458, 462, 454, 452, 453, 469, 471, 467, 403, 387, 391, 399, 397, 396, 140, 132, 134, 130, 138, 139, 137, 153, 145, 149, 151, 159, 158, 414, 446, 430, 422, 420, 421, 437, 433, 497, 481, 483, 482, 498, 502, 500, 508, 492, 493]
def region : List Vertex := [(34 : Vertex), (36 : Vertex), (37 : Vertex), (38 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (43 : Vertex), (44 : Vertex), (46 : Vertex), (48 : Vertex), (49 : Vertex), (51 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (62 : Vertex), (63 : Vertex), (96 : Vertex), (97 : Vertex), (98 : Vertex), (99 : Vertex), (103 : Vertex), (105 : Vertex), (107 : Vertex), (108 : Vertex), (109 : Vertex), (111 : Vertex), (112 : Vertex), (114 : Vertex), (115 : Vertex), (116 : Vertex), (118 : Vertex), (119 : Vertex), (120 : Vertex), (121 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (127 : Vertex), (160 : Vertex), (161 : Vertex), (163 : Vertex), (167 : Vertex), (168 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (182 : Vertex), (184 : Vertex), (186 : Vertex), (187 : Vertex), (188 : Vertex), (189 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (238 : Vertex), (240 : Vertex), (243 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (254 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (290 : Vertex), (291 : Vertex), (295 : Vertex), (296 : Vertex), (300 : Vertex), (301 : Vertex), (303 : Vertex), (306 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (314 : Vertex), (315 : Vertex), (316 : Vertex), (317 : Vertex), (352 : Vertex), (356 : Vertex), (357 : Vertex), (358 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (362 : Vertex), (363 : Vertex), (366 : Vertex), (368 : Vertex), (371 : Vertex), (373 : Vertex), (375 : Vertex), (376 : Vertex), (377 : Vertex), (378 : Vertex), (379 : Vertex), (381 : Vertex), (382 : Vertex), (424 : Vertex), (425 : Vertex), (427 : Vertex), (440 : Vertex), (443 : Vertex), (493 : Vertex), (495 : Vertex), (507 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(37 : Vertex), (38 : Vertex), (41 : Vertex), (42 : Vertex), (44 : Vertex), (49 : Vertex), (55 : Vertex), (56 : Vertex), (62 : Vertex), (97 : Vertex), (98 : Vertex), (103 : Vertex), (107 : Vertex), (109 : Vertex), (112 : Vertex), (115 : Vertex), (118 : Vertex), (121 : Vertex), (122 : Vertex), (124 : Vertex), (127 : Vertex), (161 : Vertex), (167 : Vertex), (168 : Vertex), (173 : Vertex), (176 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (247 : Vertex), (248 : Vertex), (254 : Vertex), (289 : Vertex), (290 : Vertex), (295 : Vertex), (296 : Vertex), (301 : Vertex), (307 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (352 : Vertex), (357 : Vertex), (358 : Vertex), (361 : Vertex), (362 : Vertex), (375 : Vertex), (376 : Vertex), (379 : Vertex), (381 : Vertex), (382 : Vertex), (425 : Vertex), (440 : Vertex), (443 : Vertex), (493 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(34 : Vertex), (36 : Vertex), (40 : Vertex), (43 : Vertex), (46 : Vertex), (48 : Vertex), (51 : Vertex), (53 : Vertex), (57 : Vertex), (63 : Vertex), (96 : Vertex), (99 : Vertex), (105 : Vertex), (108 : Vertex), (111 : Vertex), (114 : Vertex), (116 : Vertex), (119 : Vertex), (120 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (163 : Vertex), (175 : Vertex), (178 : Vertex), (180 : Vertex), (184 : Vertex), (187 : Vertex), (189 : Vertex), (228 : Vertex), (235 : Vertex), (238 : Vertex), (240 : Vertex), (243 : Vertex), (245 : Vertex), (249 : Vertex), (255 : Vertex), (288 : Vertex), (291 : Vertex), (300 : Vertex), (303 : Vertex), (306 : Vertex), (308 : Vertex), (315 : Vertex), (317 : Vertex), (356 : Vertex), (359 : Vertex), (360 : Vertex), (363 : Vertex), (366 : Vertex), (368 : Vertex), (371 : Vertex), (373 : Vertex), (377 : Vertex), (378 : Vertex), (424 : Vertex), (427 : Vertex), (495 : Vertex), (507 : Vertex)]
def others : List Vertex := [(34 : Vertex), (36 : Vertex), (37 : Vertex), (38 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (43 : Vertex), (44 : Vertex), (46 : Vertex), (48 : Vertex), (49 : Vertex), (51 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (62 : Vertex), (63 : Vertex), (96 : Vertex), (97 : Vertex), (98 : Vertex), (99 : Vertex), (103 : Vertex), (105 : Vertex), (107 : Vertex), (108 : Vertex), (109 : Vertex), (111 : Vertex), (112 : Vertex), (114 : Vertex), (115 : Vertex), (116 : Vertex), (118 : Vertex), (119 : Vertex), (120 : Vertex), (121 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (127 : Vertex), (160 : Vertex), (161 : Vertex), (163 : Vertex), (167 : Vertex), (168 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (182 : Vertex), (184 : Vertex), (186 : Vertex), (187 : Vertex), (188 : Vertex), (189 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (238 : Vertex), (240 : Vertex), (243 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (254 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (290 : Vertex), (291 : Vertex), (295 : Vertex), (296 : Vertex), (300 : Vertex), (301 : Vertex), (303 : Vertex), (306 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (314 : Vertex), (315 : Vertex), (316 : Vertex), (317 : Vertex), (352 : Vertex), (356 : Vertex), (357 : Vertex), (358 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (362 : Vertex), (363 : Vertex), (366 : Vertex), (368 : Vertex), (371 : Vertex), (373 : Vertex), (375 : Vertex), (376 : Vertex), (377 : Vertex), (378 : Vertex), (379 : Vertex), (381 : Vertex), (382 : Vertex), (424 : Vertex), (425 : Vertex), (427 : Vertex), (440 : Vertex), (443 : Vertex), (495 : Vertex), (507 : Vertex), (511 : Vertex)]
def head : Vertex := 493
def ban : Nat := 6284807673704095635966332905277343403004331044461429240240388232586949562115286214037686516367691884702805031224874432991225527392829755601273547304992767
def reachable : Nat := 7123000256238501463607692092928502724475034776130964137483173211134814467958260762764187781799211542987226826961611617862528355419116814345160101701091328
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
theorem evenSide_length : evenSide.length = 59 := by decide

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

end Snake9.Regrowth.E112040
