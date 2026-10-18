import RegrowthParityCounts
namespace Snake9.Regrowth.E112110
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 4, 36, 52, 60, 62, 63, 47, 43, 299, 315, 313, 312, 296, 300, 302, 294, 310, 311, 309, 293, 357, 365, 367, 383, 382, 380, 372, 368, 369, 371, 355, 354, 362, 490, 234, 226, 227, 243, 241, 240, 248, 252, 254, 255, 239, 237, 229, 228, 484, 486, 502, 503, 501, 509, 505, 489, 425, 429, 431, 423, 419, 435, 433, 432, 436, 444, 446, 442, 186, 187, 185, 189, 181, 183, 182, 166, 174, 172, 168, 160, 161, 33, 97, 96, 104, 108, 110, 102, 103, 119, 117, 125, 121, 123, 122, 114, 50, 18, 22, 23, 21, 29, 25, 9, 265, 269, 271, 263, 259, 275, 273]
def region : List Vertex := [(10 : Vertex), (14 : Vertex), (66 : Vertex), (67 : Vertex), (69 : Vertex), (74 : Vertex), (75 : Vertex), (77 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (83 : Vertex), (84 : Vertex), (88 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (133 : Vertex), (135 : Vertex), (138 : Vertex), (139 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (147 : Vertex), (148 : Vertex), (152 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (203 : Vertex), (204 : Vertex), (206 : Vertex), (210 : Vertex), (212 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (266 : Vertex), (272 : Vertex), (273 : Vertex), (276 : Vertex), (282 : Vertex), (284 : Vertex), (286 : Vertex), (320 : Vertex), (321 : Vertex), (324 : Vertex), (326 : Vertex), (328 : Vertex), (331 : Vertex), (332 : Vertex), (334 : Vertex), (338 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (349 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (392 : Vertex), (394 : Vertex), (395 : Vertex), (396 : Vertex), (398 : Vertex), (402 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (411 : Vertex), (413 : Vertex), (415 : Vertex), (448 : Vertex), (449 : Vertex), (450 : Vertex), (451 : Vertex), (453 : Vertex), (455 : Vertex), (456 : Vertex), (459 : Vertex), (460 : Vertex), (461 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (465 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (472 : Vertex), (474 : Vertex), (475 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(14 : Vertex), (67 : Vertex), (69 : Vertex), (74 : Vertex), (79 : Vertex), (81 : Vertex), (84 : Vertex), (88 : Vertex), (94 : Vertex), (131 : Vertex), (133 : Vertex), (138 : Vertex), (143 : Vertex), (145 : Vertex), (148 : Vertex), (152 : Vertex), (158 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (203 : Vertex), (206 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (266 : Vertex), (273 : Vertex), (276 : Vertex), (286 : Vertex), (321 : Vertex), (324 : Vertex), (328 : Vertex), (331 : Vertex), (334 : Vertex), (341 : Vertex), (342 : Vertex), (345 : Vertex), (346 : Vertex), (385 : Vertex), (386 : Vertex), (388 : Vertex), (392 : Vertex), (395 : Vertex), (398 : Vertex), (405 : Vertex), (406 : Vertex), (409 : Vertex), (415 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (460 : Vertex), (463 : Vertex), (465 : Vertex), (466 : Vertex), (468 : Vertex), (472 : Vertex), (475 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(10 : Vertex), (66 : Vertex), (75 : Vertex), (77 : Vertex), (80 : Vertex), (83 : Vertex), (92 : Vertex), (95 : Vertex), (130 : Vertex), (135 : Vertex), (139 : Vertex), (141 : Vertex), (144 : Vertex), (147 : Vertex), (156 : Vertex), (159 : Vertex), (192 : Vertex), (198 : Vertex), (201 : Vertex), (204 : Vertex), (210 : Vertex), (212 : Vertex), (215 : Vertex), (219 : Vertex), (221 : Vertex), (272 : Vertex), (282 : Vertex), (284 : Vertex), (320 : Vertex), (326 : Vertex), (332 : Vertex), (338 : Vertex), (343 : Vertex), (344 : Vertex), (347 : Vertex), (349 : Vertex), (384 : Vertex), (389 : Vertex), (390 : Vertex), (394 : Vertex), (396 : Vertex), (402 : Vertex), (407 : Vertex), (408 : Vertex), (411 : Vertex), (413 : Vertex), (449 : Vertex), (450 : Vertex), (455 : Vertex), (456 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (474 : Vertex), (476 : Vertex), (479 : Vertex)]
def others : List Vertex := [(10 : Vertex), (14 : Vertex), (66 : Vertex), (67 : Vertex), (69 : Vertex), (74 : Vertex), (75 : Vertex), (77 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (83 : Vertex), (84 : Vertex), (88 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (133 : Vertex), (135 : Vertex), (138 : Vertex), (139 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (147 : Vertex), (148 : Vertex), (152 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (203 : Vertex), (204 : Vertex), (206 : Vertex), (210 : Vertex), (212 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (266 : Vertex), (272 : Vertex), (276 : Vertex), (282 : Vertex), (284 : Vertex), (286 : Vertex), (320 : Vertex), (321 : Vertex), (324 : Vertex), (326 : Vertex), (328 : Vertex), (331 : Vertex), (332 : Vertex), (334 : Vertex), (338 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (349 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (392 : Vertex), (394 : Vertex), (395 : Vertex), (396 : Vertex), (398 : Vertex), (402 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (411 : Vertex), (413 : Vertex), (415 : Vertex), (448 : Vertex), (449 : Vertex), (450 : Vertex), (451 : Vertex), (453 : Vertex), (455 : Vertex), (456 : Vertex), (459 : Vertex), (460 : Vertex), (461 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (465 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (472 : Vertex), (474 : Vertex), (475 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex)]
def head : Vertex := 273
def ban : Nat := 13407807927246126992885430535009434100274082794414325196829576614808474768021516743169860046250754509282501138515002992161469195176903995616226323206224895
def reachable : Nat := 2696470106688594463196412027205283026178068180893984828913289262052030233632014251916148918407530719671483058692284687635042574330207325799859200
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
theorem oddSide_length : oddSide.length = 60 := by decide
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

end Snake9.Regrowth.E112110
