import RegrowthParityCounts
namespace Snake9.Regrowth.E112009
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[314, 315, 313, 317, 309, 311, 295, 294, 302, 300, 296, 288, 289, 417, 481, 480, 488, 492, 494, 486, 487, 503, 501, 509, 505, 507, 506, 498, 434, 432, 436, 444, 446, 447, 431, 427, 171, 187, 185, 184, 168, 172, 174, 166, 182, 183, 181, 165, 229, 237, 239, 255, 254, 252, 244, 240, 241, 243, 227, 226, 234, 106, 42, 34, 35, 51, 49, 48, 52, 60, 62, 63, 47, 45, 41, 105, 121, 125, 117, 119, 118, 374, 382, 380, 376, 368, 369, 371, 355, 363, 367, 365, 357, 356, 100, 68, 84, 92, 94, 95, 79, 75, 11, 27, 25, 29, 21, 5, 261, 269, 271, 287]
def region : List Vertex := [(0 : Vertex), (6 : Vertex), (8 : Vertex), (12 : Vertex), (14 : Vertex), (18 : Vertex), (22 : Vertex), (65 : Vertex), (66 : Vertex), (72 : Vertex), (81 : Vertex), (82 : Vertex), (83 : Vertex), (128 : Vertex), (129 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (135 : Vertex), (137 : Vertex), (138 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (154 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (204 : Vertex), (206 : Vertex), (210 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (216 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (258 : Vertex), (259 : Vertex), (266 : Vertex), (272 : Vertex), (273 : Vertex), (274 : Vertex), (275 : Vertex), (276 : Vertex), (278 : Vertex), (280 : Vertex), (284 : Vertex), (286 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex), (334 : Vertex), (338 : Vertex), (341 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (349 : Vertex), (384 : Vertex), (386 : Vertex), (387 : Vertex), (388 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (398 : Vertex), (401 : Vertex), (403 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (411 : Vertex), (413 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (461 : Vertex), (463 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (468 : Vertex), (470 : Vertex), (472 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(8 : Vertex), (14 : Vertex), (22 : Vertex), (81 : Vertex), (82 : Vertex), (128 : Vertex), (131 : Vertex), (137 : Vertex), (138 : Vertex), (143 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (158 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (206 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (259 : Vertex), (266 : Vertex), (273 : Vertex), (274 : Vertex), (276 : Vertex), (280 : Vertex), (286 : Vertex), (321 : Vertex), (322 : Vertex), (327 : Vertex), (328 : Vertex), (334 : Vertex), (341 : Vertex), (345 : Vertex), (346 : Vertex), (386 : Vertex), (388 : Vertex), (391 : Vertex), (392 : Vertex), (398 : Vertex), (403 : Vertex), (405 : Vertex), (406 : Vertex), (409 : Vertex), (410 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (463 : Vertex), (465 : Vertex), (468 : Vertex), (472 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (12 : Vertex), (18 : Vertex), (65 : Vertex), (66 : Vertex), (72 : Vertex), (83 : Vertex), (129 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (141 : Vertex), (144 : Vertex), (147 : Vertex), (154 : Vertex), (156 : Vertex), (159 : Vertex), (192 : Vertex), (198 : Vertex), (201 : Vertex), (204 : Vertex), (210 : Vertex), (215 : Vertex), (216 : Vertex), (219 : Vertex), (221 : Vertex), (258 : Vertex), (272 : Vertex), (275 : Vertex), (278 : Vertex), (284 : Vertex), (287 : Vertex), (320 : Vertex), (326 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex), (338 : Vertex), (343 : Vertex), (347 : Vertex), (349 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (401 : Vertex), (407 : Vertex), (408 : Vertex), (411 : Vertex), (413 : Vertex), (450 : Vertex), (452 : Vertex), (459 : Vertex), (461 : Vertex), (464 : Vertex), (467 : Vertex), (470 : Vertex), (476 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (6 : Vertex), (8 : Vertex), (12 : Vertex), (14 : Vertex), (18 : Vertex), (22 : Vertex), (65 : Vertex), (66 : Vertex), (72 : Vertex), (81 : Vertex), (82 : Vertex), (83 : Vertex), (128 : Vertex), (129 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (135 : Vertex), (137 : Vertex), (138 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (154 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (204 : Vertex), (206 : Vertex), (210 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (216 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (258 : Vertex), (259 : Vertex), (266 : Vertex), (272 : Vertex), (273 : Vertex), (274 : Vertex), (275 : Vertex), (276 : Vertex), (278 : Vertex), (280 : Vertex), (284 : Vertex), (286 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex), (334 : Vertex), (338 : Vertex), (341 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (349 : Vertex), (384 : Vertex), (386 : Vertex), (387 : Vertex), (388 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (398 : Vertex), (401 : Vertex), (403 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (411 : Vertex), (413 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (461 : Vertex), (463 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (468 : Vertex), (470 : Vertex), (472 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex)]
def head : Vertex := 287
def ban : Nat := 13407807927389614948913326226993750504638761116342295309766908085251730799495102121207652119534622036129048431716117421576650320895664171486781042237091518
def reachable : Nat := 2552982150660698771212095622840604704250098067956653358470033230578444855594222178632281391560983426470368629277103561916282398459652606768992577
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
theorem oddSide_length : oddSide.length = 56 := by decide
theorem evenSide_length : evenSide.length = 62 := by decide

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

end Snake9.Regrowth.E112009
