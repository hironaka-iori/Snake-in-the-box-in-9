import RegrowthParityCounts
namespace Snake9.Regrowth.E112173
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[22, 23, 21, 29, 25, 9, 265, 269, 271, 263, 259, 275, 273, 272, 276, 284, 286, 282, 346, 347, 345, 349, 341, 343, 342, 326, 334, 332, 328, 320, 321, 449, 193, 192, 200, 204, 206, 198, 199, 215, 213, 221, 217, 219, 218, 210, 466, 498, 502, 503, 501, 509, 505, 489, 425, 429, 431, 423, 419, 435, 433, 432, 436, 444, 446, 442, 186, 187, 185, 189, 181, 183, 182, 166, 174, 172, 168, 160, 161, 33, 97, 96, 104, 108, 110, 102, 103, 119, 117, 125, 121, 123, 122, 114, 50, 48, 52, 60, 62, 63, 47, 43, 299, 315, 313, 312, 296, 300, 302, 294, 310, 311]
def region : List Vertex := [(0 : Vertex), (2 : Vertex), (4 : Vertex), (10 : Vertex), (12 : Vertex), (14 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (74 : Vertex), (75 : Vertex), (77 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (83 : Vertex), (84 : Vertex), (88 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (138 : Vertex), (139 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (147 : Vertex), (148 : Vertex), (152 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (239 : Vertex), (240 : Vertex), (241 : Vertex), (243 : Vertex), (244 : Vertex), (248 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (293 : Vertex), (309 : Vertex), (311 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (362 : Vertex), (365 : Vertex), (367 : Vertex), (368 : Vertex), (369 : Vertex), (371 : Vertex), (372 : Vertex), (380 : Vertex), (382 : Vertex), (383 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (392 : Vertex), (394 : Vertex), (395 : Vertex), (396 : Vertex), (398 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (411 : Vertex), (413 : Vertex), (415 : Vertex), (452 : Vertex), (458 : Vertex), (459 : Vertex), (461 : Vertex), (463 : Vertex), (468 : Vertex), (472 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex), (480 : Vertex), (484 : Vertex), (490 : Vertex), (492 : Vertex), (494 : Vertex)]
def oddSide : List Vertex := [(2 : Vertex), (4 : Vertex), (14 : Vertex), (67 : Vertex), (69 : Vertex), (74 : Vertex), (79 : Vertex), (81 : Vertex), (84 : Vertex), (88 : Vertex), (94 : Vertex), (131 : Vertex), (133 : Vertex), (138 : Vertex), (143 : Vertex), (145 : Vertex), (148 : Vertex), (152 : Vertex), (158 : Vertex), (227 : Vertex), (229 : Vertex), (234 : Vertex), (239 : Vertex), (241 : Vertex), (244 : Vertex), (248 : Vertex), (254 : Vertex), (309 : Vertex), (355 : Vertex), (357 : Vertex), (362 : Vertex), (367 : Vertex), (369 : Vertex), (372 : Vertex), (382 : Vertex), (386 : Vertex), (388 : Vertex), (392 : Vertex), (395 : Vertex), (398 : Vertex), (405 : Vertex), (406 : Vertex), (409 : Vertex), (415 : Vertex), (458 : Vertex), (463 : Vertex), (468 : Vertex), (472 : Vertex), (478 : Vertex), (484 : Vertex), (494 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (10 : Vertex), (12 : Vertex), (66 : Vertex), (68 : Vertex), (75 : Vertex), (77 : Vertex), (80 : Vertex), (83 : Vertex), (92 : Vertex), (95 : Vertex), (130 : Vertex), (132 : Vertex), (139 : Vertex), (141 : Vertex), (144 : Vertex), (147 : Vertex), (156 : Vertex), (159 : Vertex), (226 : Vertex), (228 : Vertex), (235 : Vertex), (237 : Vertex), (240 : Vertex), (243 : Vertex), (252 : Vertex), (255 : Vertex), (293 : Vertex), (311 : Vertex), (354 : Vertex), (356 : Vertex), (365 : Vertex), (368 : Vertex), (371 : Vertex), (380 : Vertex), (383 : Vertex), (384 : Vertex), (389 : Vertex), (390 : Vertex), (394 : Vertex), (396 : Vertex), (407 : Vertex), (408 : Vertex), (411 : Vertex), (413 : Vertex), (452 : Vertex), (459 : Vertex), (461 : Vertex), (476 : Vertex), (479 : Vertex), (480 : Vertex), (490 : Vertex), (492 : Vertex)]
def others : List Vertex := [(0 : Vertex), (2 : Vertex), (4 : Vertex), (10 : Vertex), (12 : Vertex), (14 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (74 : Vertex), (75 : Vertex), (77 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (83 : Vertex), (84 : Vertex), (88 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (138 : Vertex), (139 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (147 : Vertex), (148 : Vertex), (152 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (239 : Vertex), (240 : Vertex), (241 : Vertex), (243 : Vertex), (244 : Vertex), (248 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (293 : Vertex), (309 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (362 : Vertex), (365 : Vertex), (367 : Vertex), (368 : Vertex), (369 : Vertex), (371 : Vertex), (372 : Vertex), (380 : Vertex), (382 : Vertex), (383 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (392 : Vertex), (394 : Vertex), (395 : Vertex), (396 : Vertex), (398 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (411 : Vertex), (413 : Vertex), (415 : Vertex), (452 : Vertex), (458 : Vertex), (459 : Vertex), (461 : Vertex), (463 : Vertex), (468 : Vertex), (472 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex), (480 : Vertex), (484 : Vertex), (490 : Vertex), (492 : Vertex), (494 : Vertex)]
def head : Vertex := 311
def ban : Nat := 13407740744242636560264503138903682133624349827087753532245587689747962167254549474657991091843260954268022886362597988474013531732333156353042929795705834
def reachable : Nat := 67185699960539309521859302163993855015993504639845477973753973801862818997502143883206323642473422008971823888062379740351079613413593390719210378261
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
theorem oddSide_length : oddSide.length = 51 := by decide
theorem evenSide_length : evenSide.length = 53 := by decide

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

end Snake9.Regrowth.E112173
