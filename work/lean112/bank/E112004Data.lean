import RegrowthParityCounts
namespace Snake9.Regrowth.E112004
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 3, 7, 15, 13, 29, 28, 20, 22, 18, 26, 27, 155, 219, 218, 210, 214, 212, 220, 221, 205, 207, 199, 195, 193, 192, 200, 136, 138, 142, 134, 132, 133, 149, 145, 401, 385, 387, 386, 402, 406, 404, 412, 396, 397, 399, 415, 479, 471, 469, 453, 452, 454, 462, 458, 459, 457, 473, 472, 464, 336, 272, 280, 281, 265, 267, 266, 270, 262, 260, 261, 277, 279, 275, 339, 323, 327, 335, 333, 332, 76, 68, 70, 66, 74, 75, 73, 89, 81, 85, 87, 95, 94, 350, 382, 366, 358, 356, 357, 373, 369, 305, 289, 291, 290, 306, 310, 308, 316, 300, 301]
def region : List Vertex := [(36 : Vertex), (37 : Vertex), (38 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (43 : Vertex), (46 : Vertex), (48 : Vertex), (51 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (62 : Vertex), (63 : Vertex), (96 : Vertex), (97 : Vertex), (99 : Vertex), (103 : Vertex), (104 : Vertex), (109 : Vertex), (111 : Vertex), (112 : Vertex), (114 : Vertex), (115 : Vertex), (116 : Vertex), (118 : Vertex), (120 : Vertex), (122 : Vertex), (123 : Vertex), (124 : Vertex), (125 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (163 : Vertex), (167 : Vertex), (169 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (191 : Vertex), (226 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (240 : Vertex), (241 : Vertex), (243 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (254 : Vertex), (255 : Vertex), (301 : Vertex), (303 : Vertex), (315 : Vertex), (319 : Vertex), (360 : Vertex), (361 : Vertex), (363 : Vertex), (376 : Vertex), (379 : Vertex), (416 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (426 : Vertex), (427 : Vertex), (430 : Vertex), (432 : Vertex), (435 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (445 : Vertex), (446 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (483 : Vertex), (487 : Vertex), (488 : Vertex), (492 : Vertex), (493 : Vertex), (495 : Vertex), (498 : Vertex), (499 : Vertex), (500 : Vertex), (502 : Vertex), (506 : Vertex), (507 : Vertex), (508 : Vertex), (509 : Vertex)]
def oddSide : List Vertex := [(37 : Vertex), (38 : Vertex), (41 : Vertex), (42 : Vertex), (55 : Vertex), (56 : Vertex), (62 : Vertex), (97 : Vertex), (103 : Vertex), (104 : Vertex), (109 : Vertex), (112 : Vertex), (115 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (161 : Vertex), (162 : Vertex), (167 : Vertex), (171 : Vertex), (173 : Vertex), (176 : Vertex), (179 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (191 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (241 : Vertex), (247 : Vertex), (248 : Vertex), (254 : Vertex), (301 : Vertex), (319 : Vertex), (361 : Vertex), (376 : Vertex), (379 : Vertex), (416 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (439 : Vertex), (440 : Vertex), (443 : Vertex), (445 : Vertex), (446 : Vertex), (481 : Vertex), (482 : Vertex), (487 : Vertex), (488 : Vertex), (493 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(36 : Vertex), (40 : Vertex), (43 : Vertex), (46 : Vertex), (48 : Vertex), (51 : Vertex), (53 : Vertex), (57 : Vertex), (63 : Vertex), (96 : Vertex), (99 : Vertex), (111 : Vertex), (114 : Vertex), (116 : Vertex), (120 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (163 : Vertex), (169 : Vertex), (172 : Vertex), (175 : Vertex), (178 : Vertex), (180 : Vertex), (183 : Vertex), (184 : Vertex), (189 : Vertex), (190 : Vertex), (226 : Vertex), (228 : Vertex), (235 : Vertex), (238 : Vertex), (240 : Vertex), (243 : Vertex), (245 : Vertex), (249 : Vertex), (255 : Vertex), (303 : Vertex), (315 : Vertex), (360 : Vertex), (363 : Vertex), (420 : Vertex), (423 : Vertex), (424 : Vertex), (427 : Vertex), (430 : Vertex), (432 : Vertex), (435 : Vertex), (437 : Vertex), (441 : Vertex), (442 : Vertex), (480 : Vertex), (483 : Vertex), (492 : Vertex), (495 : Vertex), (498 : Vertex), (500 : Vertex), (507 : Vertex), (509 : Vertex)]
def others : List Vertex := [(36 : Vertex), (37 : Vertex), (38 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (43 : Vertex), (46 : Vertex), (48 : Vertex), (51 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (62 : Vertex), (63 : Vertex), (96 : Vertex), (97 : Vertex), (99 : Vertex), (103 : Vertex), (104 : Vertex), (109 : Vertex), (111 : Vertex), (112 : Vertex), (114 : Vertex), (115 : Vertex), (116 : Vertex), (118 : Vertex), (120 : Vertex), (122 : Vertex), (123 : Vertex), (124 : Vertex), (125 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (163 : Vertex), (167 : Vertex), (169 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (191 : Vertex), (226 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (240 : Vertex), (241 : Vertex), (243 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (254 : Vertex), (255 : Vertex), (303 : Vertex), (315 : Vertex), (319 : Vertex), (360 : Vertex), (361 : Vertex), (363 : Vertex), (376 : Vertex), (379 : Vertex), (416 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (426 : Vertex), (427 : Vertex), (430 : Vertex), (432 : Vertex), (435 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (445 : Vertex), (446 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (483 : Vertex), (487 : Vertex), (488 : Vertex), (492 : Vertex), (493 : Vertex), (495 : Vertex), (498 : Vertex), (499 : Vertex), (500 : Vertex), (502 : Vertex), (506 : Vertex), (507 : Vertex), (508 : Vertex), (509 : Vertex)]
def head : Vertex := 301
def ban : Nat := 10246389051286543474864879081868075295942114978626122730433592833002653907767681071749776698083826669461657090606403814792305631154466109066484622869659647
def reachable : Nat := 3161418878656053624709145916337770831537250841966270647289968610719110122305865905052097600083076758228374767580082236061448251657480460879949026136424448
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

end Snake9.Regrowth.E112004
