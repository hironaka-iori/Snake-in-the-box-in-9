import RegrowthParityCounts
namespace Snake9.Regrowth.E112014
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 8, 10, 11, 27, 31, 287, 271, 269, 268, 284, 280, 282, 274, 258, 259, 257, 273, 337, 345, 347, 331, 330, 328, 320, 324, 325, 327, 343, 342, 350, 478, 222, 214, 215, 199, 197, 196, 204, 200, 202, 203, 219, 217, 209, 208, 464, 466, 450, 451, 449, 457, 461, 477, 413, 409, 411, 403, 407, 391, 389, 388, 384, 392, 394, 398, 142, 143, 141, 137, 129, 131, 130, 146, 154, 152, 156, 148, 149, 21, 85, 84, 92, 88, 90, 82, 83, 67, 65, 73, 77, 79, 78, 70, 6, 38, 34, 35, 33, 41, 45, 61, 317, 313, 315, 307, 311, 295, 293, 292, 288, 296]
def region : List Vertex := [(48 : Vertex), (52 : Vertex), (56 : Vertex), (58 : Vertex), (62 : Vertex), (96 : Vertex), (100 : Vertex), (101 : Vertex), (103 : Vertex), (104 : Vertex), (106 : Vertex), (107 : Vertex), (108 : Vertex), (112 : Vertex), (113 : Vertex), (118 : Vertex), (119 : Vertex), (121 : Vertex), (123 : Vertex), (126 : Vertex), (127 : Vertex), (160 : Vertex), (164 : Vertex), (165 : Vertex), (167 : Vertex), (168 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (176 : Vertex), (177 : Vertex), (179 : Vertex), (182 : Vertex), (183 : Vertex), (185 : Vertex), (187 : Vertex), (190 : Vertex), (191 : Vertex), (224 : Vertex), (225 : Vertex), (226 : Vertex), (227 : Vertex), (230 : Vertex), (233 : Vertex), (237 : Vertex), (238 : Vertex), (239 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (245 : Vertex), (248 : Vertex), (250 : Vertex), (252 : Vertex), (253 : Vertex), (255 : Vertex), (296 : Vertex), (298 : Vertex), (302 : Vertex), (318 : Vertex), (353 : Vertex), (354 : Vertex), (355 : Vertex), (358 : Vertex), (361 : Vertex), (364 : Vertex), (365 : Vertex), (366 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (372 : Vertex), (373 : Vertex), (376 : Vertex), (378 : Vertex), (380 : Vertex), (383 : Vertex), (417 : Vertex), (418 : Vertex), (419 : Vertex), (422 : Vertex), (425 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (431 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (436 : Vertex), (437 : Vertex), (438 : Vertex), (440 : Vertex), (442 : Vertex), (444 : Vertex), (446 : Vertex), (447 : Vertex), (480 : Vertex), (484 : Vertex), (485 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (494 : Vertex), (495 : Vertex), (497 : Vertex), (499 : Vertex), (500 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (508 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(52 : Vertex), (56 : Vertex), (62 : Vertex), (100 : Vertex), (103 : Vertex), (104 : Vertex), (107 : Vertex), (112 : Vertex), (118 : Vertex), (121 : Vertex), (127 : Vertex), (164 : Vertex), (167 : Vertex), (168 : Vertex), (171 : Vertex), (176 : Vertex), (179 : Vertex), (182 : Vertex), (185 : Vertex), (191 : Vertex), (224 : Vertex), (227 : Vertex), (230 : Vertex), (233 : Vertex), (239 : Vertex), (242 : Vertex), (244 : Vertex), (248 : Vertex), (253 : Vertex), (296 : Vertex), (302 : Vertex), (355 : Vertex), (358 : Vertex), (361 : Vertex), (364 : Vertex), (367 : Vertex), (370 : Vertex), (372 : Vertex), (376 : Vertex), (419 : Vertex), (422 : Vertex), (425 : Vertex), (428 : Vertex), (431 : Vertex), (433 : Vertex), (434 : Vertex), (436 : Vertex), (440 : Vertex), (446 : Vertex), (484 : Vertex), (487 : Vertex), (488 : Vertex), (491 : Vertex), (494 : Vertex), (499 : Vertex), (501 : Vertex), (502 : Vertex), (505 : Vertex), (506 : Vertex), (508 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(48 : Vertex), (58 : Vertex), (96 : Vertex), (101 : Vertex), (106 : Vertex), (108 : Vertex), (113 : Vertex), (119 : Vertex), (123 : Vertex), (126 : Vertex), (160 : Vertex), (165 : Vertex), (170 : Vertex), (172 : Vertex), (177 : Vertex), (183 : Vertex), (187 : Vertex), (190 : Vertex), (225 : Vertex), (226 : Vertex), (237 : Vertex), (238 : Vertex), (243 : Vertex), (245 : Vertex), (250 : Vertex), (252 : Vertex), (255 : Vertex), (298 : Vertex), (318 : Vertex), (353 : Vertex), (354 : Vertex), (365 : Vertex), (366 : Vertex), (368 : Vertex), (373 : Vertex), (378 : Vertex), (380 : Vertex), (383 : Vertex), (417 : Vertex), (418 : Vertex), (427 : Vertex), (429 : Vertex), (432 : Vertex), (437 : Vertex), (438 : Vertex), (442 : Vertex), (444 : Vertex), (447 : Vertex), (480 : Vertex), (485 : Vertex), (486 : Vertex), (490 : Vertex), (492 : Vertex), (495 : Vertex), (497 : Vertex), (500 : Vertex), (503 : Vertex), (504 : Vertex), (507 : Vertex)]
def others : List Vertex := [(48 : Vertex), (52 : Vertex), (56 : Vertex), (58 : Vertex), (62 : Vertex), (96 : Vertex), (100 : Vertex), (101 : Vertex), (103 : Vertex), (104 : Vertex), (106 : Vertex), (107 : Vertex), (108 : Vertex), (112 : Vertex), (113 : Vertex), (118 : Vertex), (119 : Vertex), (121 : Vertex), (123 : Vertex), (126 : Vertex), (127 : Vertex), (160 : Vertex), (164 : Vertex), (165 : Vertex), (167 : Vertex), (168 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (176 : Vertex), (177 : Vertex), (179 : Vertex), (182 : Vertex), (183 : Vertex), (185 : Vertex), (187 : Vertex), (190 : Vertex), (191 : Vertex), (224 : Vertex), (225 : Vertex), (226 : Vertex), (227 : Vertex), (230 : Vertex), (233 : Vertex), (237 : Vertex), (238 : Vertex), (239 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (245 : Vertex), (248 : Vertex), (250 : Vertex), (252 : Vertex), (253 : Vertex), (255 : Vertex), (298 : Vertex), (302 : Vertex), (318 : Vertex), (353 : Vertex), (354 : Vertex), (355 : Vertex), (358 : Vertex), (361 : Vertex), (364 : Vertex), (365 : Vertex), (366 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (372 : Vertex), (373 : Vertex), (376 : Vertex), (378 : Vertex), (380 : Vertex), (383 : Vertex), (417 : Vertex), (418 : Vertex), (419 : Vertex), (422 : Vertex), (425 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (431 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (436 : Vertex), (437 : Vertex), (438 : Vertex), (440 : Vertex), (442 : Vertex), (444 : Vertex), (446 : Vertex), (447 : Vertex), (480 : Vertex), (484 : Vertex), (485 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (494 : Vertex), (495 : Vertex), (497 : Vertex), (499 : Vertex), (500 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (508 : Vertex), (511 : Vertex)]
def head : Vertex := 296
def ban : Nat := 5028978126819051661204823517883952687186487999059571054019029012242350893030759981218438240579113543129847881129307489054629722561824976728320822418079743
def reachable : Nat := 8378829803123545438369201480321893440292877821532822323704532431479413137042786995583436057587789884560183977057178561799124160250121593218112826588004352
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

end Snake9.Regrowth.E112014
