import RegrowthParityCounts
namespace Snake9.Regrowth.E112164
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 2, 6, 262, 278, 274, 282, 280, 281, 265, 267, 331, 330, 322, 320, 336, 337, 339, 343, 351, 350, 348, 332, 333, 325, 261, 389, 397, 396, 412, 414, 415, 411, 403, 401, 400, 384, 386, 394, 138, 154, 152, 153, 137, 129, 131, 135, 151, 150, 148, 132, 196, 192, 208, 209, 211, 219, 203, 235, 491, 490, 482, 480, 496, 497, 499, 503, 511, 510, 508, 492, 493, 485, 229, 101, 109, 108, 124, 126, 127, 123, 115, 113, 112, 96, 98, 106, 42, 58, 56, 57, 41, 33, 35, 39, 55, 54, 52, 36, 292, 288, 304, 305, 307, 315, 319, 317, 381, 373, 372, 374, 370]
def region : List Vertex := [(12 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (19 : Vertex), (21 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (31 : Vertex), (65 : Vertex), (67 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (78 : Vertex), (79 : Vertex), (82 : Vertex), (84 : Vertex), (85 : Vertex), (86 : Vertex), (88 : Vertex), (89 : Vertex), (90 : Vertex), (93 : Vertex), (160 : Vertex), (162 : Vertex), (166 : Vertex), (168 : Vertex), (172 : Vertex), (173 : Vertex), (174 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (181 : Vertex), (187 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (191 : Vertex), (205 : Vertex), (206 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (230 : Vertex), (232 : Vertex), (238 : Vertex), (242 : Vertex), (244 : Vertex), (246 : Vertex), (248 : Vertex), (249 : Vertex), (250 : Vertex), (253 : Vertex), (302 : Vertex), (353 : Vertex), (355 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (366 : Vertex), (367 : Vertex), (370 : Vertex), (376 : Vertex), (378 : Vertex), (417 : Vertex), (419 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (430 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (437 : Vertex), (438 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (449 : Vertex), (451 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (462 : Vertex), (463 : Vertex), (466 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (472 : Vertex), (473 : Vertex), (474 : Vertex), (477 : Vertex)]
def oddSide : List Vertex := [(13 : Vertex), (19 : Vertex), (21 : Vertex), (28 : Vertex), (31 : Vertex), (67 : Vertex), (73 : Vertex), (79 : Vertex), (82 : Vertex), (84 : Vertex), (88 : Vertex), (93 : Vertex), (162 : Vertex), (168 : Vertex), (173 : Vertex), (174 : Vertex), (176 : Vertex), (179 : Vertex), (181 : Vertex), (188 : Vertex), (191 : Vertex), (205 : Vertex), (206 : Vertex), (220 : Vertex), (230 : Vertex), (242 : Vertex), (244 : Vertex), (248 : Vertex), (253 : Vertex), (302 : Vertex), (355 : Vertex), (361 : Vertex), (367 : Vertex), (370 : Vertex), (376 : Vertex), (419 : Vertex), (422 : Vertex), (425 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (440 : Vertex), (451 : Vertex), (454 : Vertex), (457 : Vertex), (463 : Vertex), (466 : Vertex), (468 : Vertex), (472 : Vertex), (477 : Vertex)]
def evenSide : List Vertex := [(12 : Vertex), (15 : Vertex), (17 : Vertex), (27 : Vertex), (29 : Vertex), (30 : Vertex), (65 : Vertex), (71 : Vertex), (72 : Vertex), (78 : Vertex), (85 : Vertex), (86 : Vertex), (89 : Vertex), (90 : Vertex), (160 : Vertex), (166 : Vertex), (172 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (187 : Vertex), (189 : Vertex), (190 : Vertex), (221 : Vertex), (222 : Vertex), (232 : Vertex), (238 : Vertex), (246 : Vertex), (249 : Vertex), (250 : Vertex), (353 : Vertex), (359 : Vertex), (360 : Vertex), (366 : Vertex), (378 : Vertex), (417 : Vertex), (423 : Vertex), (424 : Vertex), (430 : Vertex), (437 : Vertex), (438 : Vertex), (441 : Vertex), (442 : Vertex), (449 : Vertex), (455 : Vertex), (456 : Vertex), (462 : Vertex), (469 : Vertex), (470 : Vertex), (473 : Vertex), (474 : Vertex)]
def others : List Vertex := [(12 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (19 : Vertex), (21 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (31 : Vertex), (65 : Vertex), (67 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (78 : Vertex), (79 : Vertex), (82 : Vertex), (84 : Vertex), (85 : Vertex), (86 : Vertex), (88 : Vertex), (89 : Vertex), (90 : Vertex), (93 : Vertex), (160 : Vertex), (162 : Vertex), (166 : Vertex), (168 : Vertex), (172 : Vertex), (173 : Vertex), (174 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (181 : Vertex), (187 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (191 : Vertex), (205 : Vertex), (206 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (230 : Vertex), (232 : Vertex), (238 : Vertex), (242 : Vertex), (244 : Vertex), (246 : Vertex), (248 : Vertex), (249 : Vertex), (250 : Vertex), (253 : Vertex), (302 : Vertex), (353 : Vertex), (355 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (366 : Vertex), (367 : Vertex), (376 : Vertex), (378 : Vertex), (417 : Vertex), (419 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (430 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (437 : Vertex), (438 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (449 : Vertex), (451 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (462 : Vertex), (463 : Vertex), (466 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (472 : Vertex), (473 : Vertex), (474 : Vertex), (477 : Vertex)]
def head : Vertex := 370
def ban : Nat := 13407807929461456232324403735420938523578426066177900136980284349072073833453105731565108698480819822749990846000263050510506657270265131775485272804118527
def reachable : Nat := 481140867249621262784907603900939754414493240743277094649690196620441245236765599686083604940041012186223000343247225541681438170948376201965568
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
theorem oddSide_length : oddSide.length = 50 := by decide
theorem evenSide_length : evenSide.length = 51 := by decide

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

end Snake9.Regrowth.E112164
