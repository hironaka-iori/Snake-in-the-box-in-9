import RegrowthParityCounts
namespace Snake9.Regrowth.E112010
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 8, 72, 73, 65, 67, 83, 82, 80, 84, 92, 93, 95, 79, 78, 70, 6, 134, 142, 143, 159, 157, 156, 152, 144, 146, 147, 131, 129, 137, 393, 409, 411, 410, 394, 386, 384, 388, 404, 405, 407, 391, 455, 451, 467, 466, 464, 472, 476, 478, 222, 214, 215, 213, 209, 217, 219, 203, 202, 194, 192, 196, 204, 205, 461, 333, 332, 324, 320, 322, 330, 346, 347, 345, 337, 341, 343, 342, 278, 274, 272, 280, 284, 285, 287, 271, 267, 259, 257, 261, 5, 21, 17, 25, 27, 26, 30, 62, 60, 56, 48, 50, 51, 35, 39, 295, 311, 309, 308, 292, 288, 290]
def region : List Vertex := [(41 : Vertex), (42 : Vertex), (45 : Vertex), (96 : Vertex), (98 : Vertex), (100 : Vertex), (101 : Vertex), (106 : Vertex), (107 : Vertex), (108 : Vertex), (109 : Vertex), (113 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (160 : Vertex), (162 : Vertex), (164 : Vertex), (165 : Vertex), (168 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (177 : Vertex), (180 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (225 : Vertex), (227 : Vertex), (229 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (238 : Vertex), (239 : Vertex), (240 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (248 : Vertex), (250 : Vertex), (252 : Vertex), (253 : Vertex), (255 : Vertex), (290 : Vertex), (297 : Vertex), (298 : Vertex), (301 : Vertex), (302 : Vertex), (313 : Vertex), (314 : Vertex), (315 : Vertex), (353 : Vertex), (355 : Vertex), (357 : Vertex), (358 : Vertex), (360 : Vertex), (361 : Vertex), (363 : Vertex), (366 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (371 : Vertex), (376 : Vertex), (380 : Vertex), (381 : Vertex), (382 : Vertex), (383 : Vertex), (417 : Vertex), (419 : Vertex), (421 : Vertex), (422 : Vertex), (424 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (430 : Vertex), (431 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (438 : Vertex), (440 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (484 : Vertex), (485 : Vertex), (486 : Vertex), (488 : Vertex), (489 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (494 : Vertex), (495 : Vertex), (497 : Vertex), (500 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (509 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(41 : Vertex), (42 : Vertex), (98 : Vertex), (100 : Vertex), (107 : Vertex), (109 : Vertex), (117 : Vertex), (118 : Vertex), (121 : Vertex), (122 : Vertex), (162 : Vertex), (164 : Vertex), (168 : Vertex), (171 : Vertex), (173 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (227 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (239 : Vertex), (242 : Vertex), (244 : Vertex), (248 : Vertex), (253 : Vertex), (290 : Vertex), (301 : Vertex), (302 : Vertex), (313 : Vertex), (314 : Vertex), (355 : Vertex), (357 : Vertex), (358 : Vertex), (361 : Vertex), (367 : Vertex), (370 : Vertex), (376 : Vertex), (381 : Vertex), (382 : Vertex), (419 : Vertex), (421 : Vertex), (422 : Vertex), (428 : Vertex), (431 : Vertex), (433 : Vertex), (434 : Vertex), (440 : Vertex), (445 : Vertex), (446 : Vertex), (481 : Vertex), (482 : Vertex), (484 : Vertex), (488 : Vertex), (491 : Vertex), (494 : Vertex), (501 : Vertex), (502 : Vertex), (505 : Vertex), (506 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(45 : Vertex), (96 : Vertex), (101 : Vertex), (106 : Vertex), (108 : Vertex), (113 : Vertex), (119 : Vertex), (123 : Vertex), (160 : Vertex), (165 : Vertex), (170 : Vertex), (172 : Vertex), (177 : Vertex), (180 : Vertex), (183 : Vertex), (187 : Vertex), (225 : Vertex), (231 : Vertex), (232 : Vertex), (238 : Vertex), (240 : Vertex), (243 : Vertex), (250 : Vertex), (252 : Vertex), (255 : Vertex), (297 : Vertex), (298 : Vertex), (315 : Vertex), (353 : Vertex), (360 : Vertex), (363 : Vertex), (366 : Vertex), (368 : Vertex), (371 : Vertex), (380 : Vertex), (383 : Vertex), (417 : Vertex), (424 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (432 : Vertex), (435 : Vertex), (438 : Vertex), (444 : Vertex), (447 : Vertex), (480 : Vertex), (485 : Vertex), (486 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex), (495 : Vertex), (497 : Vertex), (500 : Vertex), (503 : Vertex), (507 : Vertex), (509 : Vertex)]
def others : List Vertex := [(41 : Vertex), (42 : Vertex), (45 : Vertex), (96 : Vertex), (98 : Vertex), (100 : Vertex), (101 : Vertex), (106 : Vertex), (107 : Vertex), (108 : Vertex), (109 : Vertex), (113 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (160 : Vertex), (162 : Vertex), (164 : Vertex), (165 : Vertex), (168 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (177 : Vertex), (180 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (225 : Vertex), (227 : Vertex), (229 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (238 : Vertex), (239 : Vertex), (240 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (248 : Vertex), (250 : Vertex), (252 : Vertex), (253 : Vertex), (255 : Vertex), (297 : Vertex), (298 : Vertex), (301 : Vertex), (302 : Vertex), (313 : Vertex), (314 : Vertex), (315 : Vertex), (353 : Vertex), (355 : Vertex), (357 : Vertex), (358 : Vertex), (360 : Vertex), (361 : Vertex), (363 : Vertex), (366 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (371 : Vertex), (376 : Vertex), (380 : Vertex), (381 : Vertex), (382 : Vertex), (383 : Vertex), (417 : Vertex), (419 : Vertex), (421 : Vertex), (422 : Vertex), (424 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (430 : Vertex), (431 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (438 : Vertex), (440 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (484 : Vertex), (485 : Vertex), (486 : Vertex), (488 : Vertex), (489 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (494 : Vertex), (495 : Vertex), (497 : Vertex), (500 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (509 : Vertex), (511 : Vertex)]
def head : Vertex := 290
def ban : Nat := 4244999858745991060020637254266871063139677931507409572494094684160151671298147633849574327636017018481275897284938059263556434776190231835703322077036543
def reachable : Nat := 9162808071196606039553387743938975064339687889084983805229466759561612358775399342952299970530886409208755960901547991590197448035756338110730326929047552
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
theorem evenSide_length : evenSide.length = 58 := by decide

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

end Snake9.Regrowth.E112010
