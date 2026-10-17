import RegrowthParityCounts
namespace Snake9.Regrowth.E112227
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[122, 123, 121, 125, 117, 119, 118, 102, 110, 108, 104, 96, 97, 33, 161, 160, 168, 172, 174, 166, 182, 183, 181, 189, 185, 187, 186, 442, 446, 444, 436, 432, 433, 435, 419, 423, 431, 429, 425, 489, 505, 509, 501, 503, 502, 498, 466, 210, 218, 219, 217, 221, 213, 215, 199, 198, 206, 204, 200, 192, 193, 449, 321, 320, 328, 332, 334, 326, 342, 343, 341, 349, 345, 347, 346, 282, 286, 284, 276, 272, 273, 275, 259, 263, 271, 269, 265, 9, 25, 29, 21, 23, 22, 18, 50, 48, 52, 60, 62, 63, 47, 43, 299, 315, 313, 312, 296, 300, 302, 294, 310, 311]
def region : List Vertex := [(0 : Vertex), (4 : Vertex), (10 : Vertex), (12 : Vertex), (14 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (74 : Vertex), (75 : Vertex), (77 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (83 : Vertex), (84 : Vertex), (88 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (138 : Vertex), (139 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (147 : Vertex), (148 : Vertex), (152 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (239 : Vertex), (240 : Vertex), (241 : Vertex), (243 : Vertex), (244 : Vertex), (248 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (293 : Vertex), (309 : Vertex), (311 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (359 : Vertex), (362 : Vertex), (365 : Vertex), (367 : Vertex), (368 : Vertex), (369 : Vertex), (371 : Vertex), (372 : Vertex), (380 : Vertex), (382 : Vertex), (383 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (392 : Vertex), (394 : Vertex), (395 : Vertex), (396 : Vertex), (398 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (411 : Vertex), (413 : Vertex), (415 : Vertex), (452 : Vertex), (458 : Vertex), (459 : Vertex), (461 : Vertex), (463 : Vertex), (468 : Vertex), (472 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex), (480 : Vertex), (484 : Vertex), (490 : Vertex), (492 : Vertex), (494 : Vertex)]
def oddSide : List Vertex := [(4 : Vertex), (14 : Vertex), (67 : Vertex), (69 : Vertex), (74 : Vertex), (79 : Vertex), (81 : Vertex), (84 : Vertex), (88 : Vertex), (94 : Vertex), (131 : Vertex), (133 : Vertex), (138 : Vertex), (143 : Vertex), (145 : Vertex), (148 : Vertex), (152 : Vertex), (158 : Vertex), (227 : Vertex), (229 : Vertex), (234 : Vertex), (239 : Vertex), (241 : Vertex), (244 : Vertex), (248 : Vertex), (254 : Vertex), (309 : Vertex), (355 : Vertex), (357 : Vertex), (362 : Vertex), (367 : Vertex), (369 : Vertex), (372 : Vertex), (382 : Vertex), (386 : Vertex), (388 : Vertex), (392 : Vertex), (395 : Vertex), (398 : Vertex), (405 : Vertex), (406 : Vertex), (409 : Vertex), (415 : Vertex), (458 : Vertex), (463 : Vertex), (468 : Vertex), (472 : Vertex), (478 : Vertex), (484 : Vertex), (494 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (10 : Vertex), (12 : Vertex), (66 : Vertex), (68 : Vertex), (75 : Vertex), (77 : Vertex), (80 : Vertex), (83 : Vertex), (92 : Vertex), (95 : Vertex), (130 : Vertex), (132 : Vertex), (139 : Vertex), (141 : Vertex), (144 : Vertex), (147 : Vertex), (156 : Vertex), (159 : Vertex), (226 : Vertex), (228 : Vertex), (235 : Vertex), (237 : Vertex), (240 : Vertex), (243 : Vertex), (252 : Vertex), (255 : Vertex), (293 : Vertex), (311 : Vertex), (354 : Vertex), (356 : Vertex), (359 : Vertex), (365 : Vertex), (368 : Vertex), (371 : Vertex), (380 : Vertex), (383 : Vertex), (384 : Vertex), (389 : Vertex), (390 : Vertex), (394 : Vertex), (396 : Vertex), (407 : Vertex), (408 : Vertex), (411 : Vertex), (413 : Vertex), (452 : Vertex), (459 : Vertex), (461 : Vertex), (476 : Vertex), (479 : Vertex), (480 : Vertex), (490 : Vertex), (492 : Vertex)]
def others : List Vertex := [(0 : Vertex), (4 : Vertex), (10 : Vertex), (12 : Vertex), (14 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (74 : Vertex), (75 : Vertex), (77 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (83 : Vertex), (84 : Vertex), (88 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (138 : Vertex), (139 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (147 : Vertex), (148 : Vertex), (152 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (239 : Vertex), (240 : Vertex), (241 : Vertex), (243 : Vertex), (244 : Vertex), (248 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (293 : Vertex), (309 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (359 : Vertex), (362 : Vertex), (365 : Vertex), (367 : Vertex), (368 : Vertex), (369 : Vertex), (371 : Vertex), (372 : Vertex), (380 : Vertex), (382 : Vertex), (383 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (392 : Vertex), (394 : Vertex), (395 : Vertex), (396 : Vertex), (398 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (411 : Vertex), (413 : Vertex), (415 : Vertex), (452 : Vertex), (458 : Vertex), (459 : Vertex), (461 : Vertex), (463 : Vertex), (468 : Vertex), (472 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex), (480 : Vertex), (484 : Vertex), (490 : Vertex), (492 : Vertex), (494 : Vertex)]
def head : Vertex := 311
def ban : Nat := 13407740744242636560264503138903682133624349825913482240858671075803221868859880960970149817389101018914377400596493475916709310000483657160658578279738350
def reachable : Nat := 67185699960539309521859302163993855015994678911136864890367918542161213666015831724480777802408775654457589992574937044572811462912785775070726345745
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
theorem evenSide_length : evenSide.length = 54 := by decide

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

end Snake9.Regrowth.E112227
