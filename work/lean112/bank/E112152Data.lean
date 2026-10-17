import RegrowthParityCounts
namespace Snake9.Regrowth.E112152
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 2, 6, 262, 278, 276, 277, 261, 257, 259, 267, 283, 282, 280, 264, 328, 320, 322, 338, 339, 337, 345, 349, 348, 350, 334, 335, 327, 455, 199, 207, 206, 222, 220, 221, 213, 209, 211, 210, 194, 192, 200, 201, 457, 459, 475, 474, 472, 464, 468, 452, 388, 384, 386, 394, 398, 414, 412, 413, 409, 401, 403, 407, 151, 150, 148, 144, 152, 154, 155, 139, 131, 129, 133, 141, 140, 12, 76, 77, 69, 65, 67, 75, 74, 90, 88, 80, 84, 86, 87, 95, 31, 63, 59, 58, 56, 48, 52, 36, 292, 288, 290, 298, 302, 318, 316, 317, 313, 305, 307, 311, 375]
def region : List Vertex := [(9 : Vertex), (17 : Vertex), (19 : Vertex), (25 : Vertex), (33 : Vertex), (35 : Vertex), (39 : Vertex), (41 : Vertex), (45 : Vertex), (96 : Vertex), (98 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (110 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (117 : Vertex), (121 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (162 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (170 : Vertex), (174 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (181 : Vertex), (185 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (225 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (237 : Vertex), (240 : Vertex), (244 : Vertex), (246 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (255 : Vertex), (353 : Vertex), (355 : Vertex), (357 : Vertex), (358 : Vertex), (361 : Vertex), (363 : Vertex), (364 : Vertex), (365 : Vertex), (368 : Vertex), (372 : Vertex), (373 : Vertex), (374 : Vertex), (375 : Vertex), (376 : Vertex), (378 : Vertex), (379 : Vertex), (383 : Vertex), (417 : Vertex), (419 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (431 : Vertex), (432 : Vertex), (434 : Vertex), (436 : Vertex), (437 : Vertex), (438 : Vertex), (440 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (483 : Vertex), (485 : Vertex), (486 : Vertex), (488 : Vertex), (490 : Vertex), (492 : Vertex), (493 : Vertex), (494 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (505 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(19 : Vertex), (25 : Vertex), (35 : Vertex), (41 : Vertex), (98 : Vertex), (103 : Vertex), (104 : Vertex), (110 : Vertex), (115 : Vertex), (117 : Vertex), (121 : Vertex), (124 : Vertex), (162 : Vertex), (167 : Vertex), (168 : Vertex), (174 : Vertex), (179 : Vertex), (181 : Vertex), (185 : Vertex), (188 : Vertex), (227 : Vertex), (229 : Vertex), (230 : Vertex), (234 : Vertex), (236 : Vertex), (244 : Vertex), (247 : Vertex), (248 : Vertex), (251 : Vertex), (355 : Vertex), (357 : Vertex), (358 : Vertex), (361 : Vertex), (364 : Vertex), (372 : Vertex), (375 : Vertex), (376 : Vertex), (379 : Vertex), (419 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (428 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (440 : Vertex), (443 : Vertex), (481 : Vertex), (482 : Vertex), (488 : Vertex), (493 : Vertex), (494 : Vertex), (499 : Vertex), (501 : Vertex), (502 : Vertex), (505 : Vertex), (508 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(9 : Vertex), (17 : Vertex), (33 : Vertex), (39 : Vertex), (45 : Vertex), (96 : Vertex), (102 : Vertex), (105 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (166 : Vertex), (169 : Vertex), (170 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (189 : Vertex), (190 : Vertex), (225 : Vertex), (228 : Vertex), (235 : Vertex), (237 : Vertex), (240 : Vertex), (246 : Vertex), (249 : Vertex), (250 : Vertex), (255 : Vertex), (353 : Vertex), (363 : Vertex), (365 : Vertex), (368 : Vertex), (373 : Vertex), (374 : Vertex), (378 : Vertex), (383 : Vertex), (417 : Vertex), (423 : Vertex), (424 : Vertex), (427 : Vertex), (429 : Vertex), (432 : Vertex), (437 : Vertex), (438 : Vertex), (442 : Vertex), (447 : Vertex), (480 : Vertex), (483 : Vertex), (485 : Vertex), (486 : Vertex), (490 : Vertex), (492 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (503 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(9 : Vertex), (17 : Vertex), (19 : Vertex), (25 : Vertex), (33 : Vertex), (35 : Vertex), (39 : Vertex), (41 : Vertex), (45 : Vertex), (96 : Vertex), (98 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (110 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (117 : Vertex), (121 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (162 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (170 : Vertex), (174 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (181 : Vertex), (185 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (225 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (237 : Vertex), (240 : Vertex), (244 : Vertex), (246 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (255 : Vertex), (353 : Vertex), (355 : Vertex), (357 : Vertex), (358 : Vertex), (361 : Vertex), (363 : Vertex), (364 : Vertex), (365 : Vertex), (368 : Vertex), (372 : Vertex), (373 : Vertex), (374 : Vertex), (376 : Vertex), (378 : Vertex), (379 : Vertex), (383 : Vertex), (417 : Vertex), (419 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (431 : Vertex), (432 : Vertex), (434 : Vertex), (436 : Vertex), (437 : Vertex), (438 : Vertex), (440 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (483 : Vertex), (485 : Vertex), (486 : Vertex), (488 : Vertex), (490 : Vertex), (492 : Vertex), (493 : Vertex), (494 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (505 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex), (511 : Vertex)]
def head : Vertex := 375
def ban : Nat := 684351668293115764056983466686579000546756461959775682956954553736778413766149237109525814120598691774141513152919753452484851473888746934446299117125119
def reachable : Nat := 12723456261649481335517041531519267126932609358632617694766606889984985616307397739692348484046304735915890345033566297401269031338057823011987349888958976
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

end Snake9.Regrowth.E112152
