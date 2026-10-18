import RegrowthParityCounts
namespace Snake9.Regrowth.E112088
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 16, 18, 19, 3, 7, 5, 13, 29, 28, 30, 14, 78, 70, 68, 84, 85, 87, 95, 91, 90, 88, 72, 73, 65, 193, 449, 457, 456, 472, 474, 475, 467, 471, 469, 468, 452, 454, 462, 463, 207, 205, 221, 220, 222, 214, 210, 194, 130, 134, 132, 140, 136, 152, 154, 155, 159, 151, 149, 145, 401, 400, 402, 406, 414, 412, 413, 397, 389, 391, 387, 395, 394, 266, 330, 331, 323, 327, 325, 333, 332, 348, 350, 342, 338, 336, 337, 345, 281, 313, 317, 316, 318, 310, 306, 290, 34, 38, 36, 44, 40, 56, 58, 59, 63, 55, 53, 49, 113, 112, 114, 118]
def region : List Vertex := [(99 : Vertex), (101 : Vertex), (103 : Vertex), (106 : Vertex), (107 : Vertex), (109 : Vertex), (111 : Vertex), (118 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (161 : Vertex), (163 : Vertex), (165 : Vertex), (167 : Vertex), (169 : Vertex), (170 : Vertex), (171 : Vertex), (173 : Vertex), (174 : Vertex), (175 : Vertex), (176 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (182 : Vertex), (185 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (224 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (243 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (255 : Vertex), (257 : Vertex), (260 : Vertex), (262 : Vertex), (271 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (287 : Vertex), (289 : Vertex), (293 : Vertex), (295 : Vertex), (299 : Vertex), (303 : Vertex), (352 : Vertex), (353 : Vertex), (356 : Vertex), (358 : Vertex), (360 : Vertex), (361 : Vertex), (366 : Vertex), (367 : Vertex), (371 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (376 : Vertex), (378 : Vertex), (379 : Vertex), (383 : Vertex), (416 : Vertex), (417 : Vertex), (420 : Vertex), (422 : Vertex), (424 : Vertex), (425 : Vertex), (428 : Vertex), (430 : Vertex), (431 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (482 : Vertex), (483 : Vertex), (485 : Vertex), (487 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (502 : Vertex), (505 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(103 : Vertex), (107 : Vertex), (109 : Vertex), (118 : Vertex), (124 : Vertex), (161 : Vertex), (167 : Vertex), (171 : Vertex), (173 : Vertex), (174 : Vertex), (176 : Vertex), (179 : Vertex), (182 : Vertex), (185 : Vertex), (188 : Vertex), (224 : Vertex), (227 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (244 : Vertex), (247 : Vertex), (248 : Vertex), (251 : Vertex), (262 : Vertex), (271 : Vertex), (276 : Vertex), (279 : Vertex), (289 : Vertex), (295 : Vertex), (299 : Vertex), (352 : Vertex), (358 : Vertex), (361 : Vertex), (367 : Vertex), (372 : Vertex), (375 : Vertex), (376 : Vertex), (379 : Vertex), (416 : Vertex), (422 : Vertex), (425 : Vertex), (428 : Vertex), (431 : Vertex), (436 : Vertex), (439 : Vertex), (440 : Vertex), (443 : Vertex), (482 : Vertex), (487 : Vertex), (491 : Vertex), (493 : Vertex), (496 : Vertex), (502 : Vertex), (505 : Vertex), (508 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(99 : Vertex), (101 : Vertex), (106 : Vertex), (111 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (163 : Vertex), (165 : Vertex), (169 : Vertex), (170 : Vertex), (175 : Vertex), (178 : Vertex), (180 : Vertex), (189 : Vertex), (190 : Vertex), (228 : Vertex), (231 : Vertex), (232 : Vertex), (235 : Vertex), (238 : Vertex), (243 : Vertex), (245 : Vertex), (249 : Vertex), (250 : Vertex), (255 : Vertex), (257 : Vertex), (260 : Vertex), (277 : Vertex), (287 : Vertex), (293 : Vertex), (303 : Vertex), (353 : Vertex), (356 : Vertex), (360 : Vertex), (366 : Vertex), (371 : Vertex), (373 : Vertex), (378 : Vertex), (383 : Vertex), (417 : Vertex), (420 : Vertex), (424 : Vertex), (430 : Vertex), (435 : Vertex), (437 : Vertex), (442 : Vertex), (447 : Vertex), (480 : Vertex), (483 : Vertex), (485 : Vertex), (490 : Vertex), (492 : Vertex), (497 : Vertex), (498 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(99 : Vertex), (101 : Vertex), (103 : Vertex), (106 : Vertex), (107 : Vertex), (109 : Vertex), (111 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (161 : Vertex), (163 : Vertex), (165 : Vertex), (167 : Vertex), (169 : Vertex), (170 : Vertex), (171 : Vertex), (173 : Vertex), (174 : Vertex), (175 : Vertex), (176 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (182 : Vertex), (185 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (224 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (243 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (255 : Vertex), (257 : Vertex), (260 : Vertex), (262 : Vertex), (271 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (287 : Vertex), (289 : Vertex), (293 : Vertex), (295 : Vertex), (299 : Vertex), (303 : Vertex), (352 : Vertex), (353 : Vertex), (356 : Vertex), (358 : Vertex), (360 : Vertex), (361 : Vertex), (366 : Vertex), (367 : Vertex), (371 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (376 : Vertex), (378 : Vertex), (379 : Vertex), (383 : Vertex), (416 : Vertex), (417 : Vertex), (420 : Vertex), (422 : Vertex), (424 : Vertex), (425 : Vertex), (428 : Vertex), (430 : Vertex), (431 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (482 : Vertex), (483 : Vertex), (485 : Vertex), (487 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (502 : Vertex), (505 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex), (511 : Vertex)]
def head : Vertex := 118
def ban : Nat := 718665335225964590625061931257611679745814436039554222191751527218269966082973272598702938520220362569807852959163125921098720542432236784986551905943551
def reachable : Nat := 12689142594716632508948963066948234447733551384552839155531809916503494063990573704203171359646683065120224005227322924932655162269514333161447097100140544
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
theorem evenSide_length : evenSide.length = 57 := by decide

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

end Snake9.Regrowth.E112088
