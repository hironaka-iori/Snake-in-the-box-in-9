import RegrowthParityCounts
namespace Snake9.Regrowth.E112060
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 2, 18, 82, 90, 88, 72, 73, 75, 67, 71, 70, 68, 84, 85, 21, 17, 25, 27, 31, 15, 14, 12, 28, 284, 280, 264, 265, 267, 259, 263, 261, 325, 333, 332, 334, 330, 322, 320, 336, 337, 345, 347, 351, 343, 342, 278, 406, 407, 415, 411, 409, 401, 385, 384, 386, 394, 398, 396, 397, 141, 137, 139, 131, 135, 134, 132, 148, 144, 152, 154, 158, 222, 206, 202, 194, 192, 193, 197, 229, 485, 493, 492, 494, 490, 482, 480, 496, 497, 505, 507, 511, 503, 502, 246, 118, 119, 127, 123, 121, 113, 97, 96, 98, 106, 110, 108, 109, 45, 41, 43, 35]
def region : List Vertex := [(35 : Vertex), (36 : Vertex), (38 : Vertex), (39 : Vertex), (48 : Vertex), (51 : Vertex), (52 : Vertex), (56 : Vertex), (58 : Vertex), (62 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (168 : Vertex), (170 : Vertex), (172 : Vertex), (174 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (181 : Vertex), (183 : Vertex), (185 : Vertex), (187 : Vertex), (188 : Vertex), (189 : Vertex), (191 : Vertex), (211 : Vertex), (215 : Vertex), (217 : Vertex), (219 : Vertex), (221 : Vertex), (227 : Vertex), (232 : Vertex), (233 : Vertex), (235 : Vertex), (239 : Vertex), (243 : Vertex), (248 : Vertex), (250 : Vertex), (252 : Vertex), (253 : Vertex), (288 : Vertex), (289 : Vertex), (290 : Vertex), (292 : Vertex), (294 : Vertex), (298 : Vertex), (300 : Vertex), (302 : Vertex), (303 : Vertex), (304 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (308 : Vertex), (309 : Vertex), (311 : Vertex), (313 : Vertex), (314 : Vertex), (315 : Vertex), (317 : Vertex), (318 : Vertex), (319 : Vertex), (355 : Vertex), (356 : Vertex), (358 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (363 : Vertex), (367 : Vertex), (370 : Vertex), (371 : Vertex), (372 : Vertex), (373 : Vertex), (376 : Vertex), (378 : Vertex), (380 : Vertex), (381 : Vertex), (382 : Vertex), (419 : Vertex), (420 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (427 : Vertex), (431 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (440 : Vertex), (442 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (451 : Vertex), (452 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (459 : Vertex), (463 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (469 : Vertex), (472 : Vertex), (474 : Vertex), (476 : Vertex), (477 : Vertex)]
def oddSide : List Vertex := [(35 : Vertex), (38 : Vertex), (52 : Vertex), (56 : Vertex), (62 : Vertex), (161 : Vertex), (162 : Vertex), (168 : Vertex), (174 : Vertex), (179 : Vertex), (181 : Vertex), (185 : Vertex), (188 : Vertex), (191 : Vertex), (211 : Vertex), (217 : Vertex), (227 : Vertex), (233 : Vertex), (239 : Vertex), (248 : Vertex), (253 : Vertex), (289 : Vertex), (290 : Vertex), (292 : Vertex), (302 : Vertex), (304 : Vertex), (307 : Vertex), (309 : Vertex), (313 : Vertex), (314 : Vertex), (319 : Vertex), (355 : Vertex), (358 : Vertex), (361 : Vertex), (367 : Vertex), (370 : Vertex), (372 : Vertex), (376 : Vertex), (381 : Vertex), (382 : Vertex), (419 : Vertex), (422 : Vertex), (425 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (440 : Vertex), (445 : Vertex), (446 : Vertex), (451 : Vertex), (454 : Vertex), (457 : Vertex), (463 : Vertex), (466 : Vertex), (468 : Vertex), (472 : Vertex), (477 : Vertex)]
def evenSide : List Vertex := [(36 : Vertex), (39 : Vertex), (48 : Vertex), (51 : Vertex), (58 : Vertex), (160 : Vertex), (170 : Vertex), (172 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (183 : Vertex), (187 : Vertex), (189 : Vertex), (215 : Vertex), (219 : Vertex), (221 : Vertex), (232 : Vertex), (235 : Vertex), (243 : Vertex), (250 : Vertex), (252 : Vertex), (288 : Vertex), (294 : Vertex), (298 : Vertex), (300 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (308 : Vertex), (311 : Vertex), (315 : Vertex), (317 : Vertex), (318 : Vertex), (356 : Vertex), (359 : Vertex), (360 : Vertex), (363 : Vertex), (371 : Vertex), (373 : Vertex), (378 : Vertex), (380 : Vertex), (420 : Vertex), (423 : Vertex), (424 : Vertex), (427 : Vertex), (435 : Vertex), (437 : Vertex), (442 : Vertex), (444 : Vertex), (452 : Vertex), (455 : Vertex), (456 : Vertex), (459 : Vertex), (467 : Vertex), (469 : Vertex), (474 : Vertex), (476 : Vertex)]
def others : List Vertex := [(36 : Vertex), (38 : Vertex), (39 : Vertex), (48 : Vertex), (51 : Vertex), (52 : Vertex), (56 : Vertex), (58 : Vertex), (62 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (168 : Vertex), (170 : Vertex), (172 : Vertex), (174 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (181 : Vertex), (183 : Vertex), (185 : Vertex), (187 : Vertex), (188 : Vertex), (189 : Vertex), (191 : Vertex), (211 : Vertex), (215 : Vertex), (217 : Vertex), (219 : Vertex), (221 : Vertex), (227 : Vertex), (232 : Vertex), (233 : Vertex), (235 : Vertex), (239 : Vertex), (243 : Vertex), (248 : Vertex), (250 : Vertex), (252 : Vertex), (253 : Vertex), (288 : Vertex), (289 : Vertex), (290 : Vertex), (292 : Vertex), (294 : Vertex), (298 : Vertex), (300 : Vertex), (302 : Vertex), (303 : Vertex), (304 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (308 : Vertex), (309 : Vertex), (311 : Vertex), (313 : Vertex), (314 : Vertex), (315 : Vertex), (317 : Vertex), (318 : Vertex), (319 : Vertex), (355 : Vertex), (356 : Vertex), (358 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (363 : Vertex), (367 : Vertex), (370 : Vertex), (371 : Vertex), (372 : Vertex), (373 : Vertex), (376 : Vertex), (378 : Vertex), (380 : Vertex), (381 : Vertex), (382 : Vertex), (419 : Vertex), (420 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (427 : Vertex), (431 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (440 : Vertex), (442 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (451 : Vertex), (452 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (459 : Vertex), (463 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (469 : Vertex), (472 : Vertex), (474 : Vertex), (476 : Vertex), (477 : Vertex)]
def head : Vertex := 35
def ban : Nat := 13407807929293413527699101725349642379950928581704301942370138264386342329911016103034050433464820395363137078915294115163016902802408844252359133587570687
def reachable : Nat := 649183571874923272856203747528437238888091435353423179335421700162530873767823864702083032326894779271191935690736980009537725694074515418513408
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
theorem oddSide_length : oddSide.length = 57 := by decide
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

end Snake9.Regrowth.E112060
