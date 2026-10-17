import RegrowthParityCounts
namespace Snake9.Regrowth.E112020
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 257, 265, 264, 266, 270, 262, 260, 276, 277, 285, 287, 283, 275, 274, 18, 146, 147, 155, 159, 157, 149, 133, 132, 134, 142, 138, 136, 137, 201, 205, 207, 199, 195, 194, 192, 208, 212, 220, 222, 218, 474, 458, 462, 454, 452, 453, 469, 471, 407, 406, 414, 412, 396, 397, 399, 395, 387, 386, 384, 400, 401, 409, 473, 345, 337, 336, 320, 322, 323, 327, 335, 333, 332, 348, 350, 342, 86, 70, 68, 69, 85, 93, 95, 91, 75, 74, 72, 88, 24, 28, 12, 13, 15, 7, 23, 55, 311, 310, 318, 316, 312, 304, 288, 290, 291, 299, 303, 301, 293, 37]
def region : List Vertex := [(36 : Vertex), (37 : Vertex), (38 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (46 : Vertex), (49 : Vertex), (52 : Vertex), (57 : Vertex), (58 : Vertex), (59 : Vertex), (61 : Vertex), (96 : Vertex), (97 : Vertex), (98 : Vertex), (99 : Vertex), (103 : Vertex), (105 : Vertex), (108 : Vertex), (109 : Vertex), (110 : Vertex), (111 : Vertex), (112 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (116 : Vertex), (121 : Vertex), (122 : Vertex), (124 : Vertex), (126 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (163 : Vertex), (167 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (180 : Vertex), (182 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (190 : Vertex), (225 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (232 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (241 : Vertex), (242 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (253 : Vertex), (255 : Vertex), (353 : Vertex), (356 : Vertex), (358 : Vertex), (360 : Vertex), (361 : Vertex), (362 : Vertex), (366 : Vertex), (370 : Vertex), (371 : Vertex), (372 : Vertex), (373 : Vertex), (378 : Vertex), (379 : Vertex), (381 : Vertex), (383 : Vertex), (417 : Vertex), (420 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (426 : Vertex), (430 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (442 : Vertex), (443 : Vertex), (445 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (483 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (495 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (500 : Vertex), (502 : Vertex), (504 : Vertex), (507 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(37 : Vertex), (38 : Vertex), (41 : Vertex), (42 : Vertex), (49 : Vertex), (52 : Vertex), (59 : Vertex), (61 : Vertex), (97 : Vertex), (98 : Vertex), (103 : Vertex), (109 : Vertex), (110 : Vertex), (112 : Vertex), (115 : Vertex), (121 : Vertex), (122 : Vertex), (124 : Vertex), (161 : Vertex), (162 : Vertex), (167 : Vertex), (171 : Vertex), (173 : Vertex), (176 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (229 : Vertex), (230 : Vertex), (234 : Vertex), (236 : Vertex), (241 : Vertex), (242 : Vertex), (247 : Vertex), (248 : Vertex), (251 : Vertex), (253 : Vertex), (358 : Vertex), (361 : Vertex), (362 : Vertex), (370 : Vertex), (372 : Vertex), (379 : Vertex), (381 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (434 : Vertex), (436 : Vertex), (443 : Vertex), (445 : Vertex), (481 : Vertex), (482 : Vertex), (487 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex), (496 : Vertex), (499 : Vertex), (502 : Vertex), (508 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(36 : Vertex), (40 : Vertex), (46 : Vertex), (57 : Vertex), (58 : Vertex), (96 : Vertex), (99 : Vertex), (105 : Vertex), (108 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (116 : Vertex), (126 : Vertex), (160 : Vertex), (163 : Vertex), (172 : Vertex), (175 : Vertex), (177 : Vertex), (180 : Vertex), (184 : Vertex), (190 : Vertex), (225 : Vertex), (228 : Vertex), (232 : Vertex), (235 : Vertex), (238 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (249 : Vertex), (255 : Vertex), (353 : Vertex), (356 : Vertex), (360 : Vertex), (366 : Vertex), (371 : Vertex), (373 : Vertex), (378 : Vertex), (383 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex), (424 : Vertex), (430 : Vertex), (435 : Vertex), (437 : Vertex), (442 : Vertex), (447 : Vertex), (480 : Vertex), (483 : Vertex), (489 : Vertex), (492 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (500 : Vertex), (504 : Vertex), (507 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(36 : Vertex), (38 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (46 : Vertex), (49 : Vertex), (52 : Vertex), (57 : Vertex), (58 : Vertex), (59 : Vertex), (61 : Vertex), (96 : Vertex), (97 : Vertex), (98 : Vertex), (99 : Vertex), (103 : Vertex), (105 : Vertex), (108 : Vertex), (109 : Vertex), (110 : Vertex), (111 : Vertex), (112 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (116 : Vertex), (121 : Vertex), (122 : Vertex), (124 : Vertex), (126 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (163 : Vertex), (167 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (180 : Vertex), (182 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (190 : Vertex), (225 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (232 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (241 : Vertex), (242 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (253 : Vertex), (255 : Vertex), (353 : Vertex), (356 : Vertex), (358 : Vertex), (360 : Vertex), (361 : Vertex), (362 : Vertex), (366 : Vertex), (370 : Vertex), (371 : Vertex), (372 : Vertex), (373 : Vertex), (378 : Vertex), (379 : Vertex), (381 : Vertex), (383 : Vertex), (417 : Vertex), (420 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (426 : Vertex), (430 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (442 : Vertex), (443 : Vertex), (445 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (483 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (495 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (500 : Vertex), (502 : Vertex), (504 : Vertex), (507 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex), (511 : Vertex)]
def head : Vertex := 37
def ban : Nat := 347034100593341124232270824747278043578422336755407750675797954774259209177073125551038755866535474385707409958724188244309997415450697083305912134795263
def reachable : Nat := 13060773829349255975341754173458568083900943483836985627047763488947504820896473851250835542300367953304324448227761862609443885396495872863127736871288832
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
theorem oddSide_length : oddSide.length = 63 := by decide
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

end Snake9.Regrowth.E112020
