import RegrowthParityCounts
namespace Snake9.Regrowth.E112005
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[122, 114, 118, 116, 124, 125, 109, 111, 103, 99, 97, 96, 104, 360, 361, 363, 379, 507, 506, 498, 502, 500, 508, 492, 493, 495, 487, 483, 481, 480, 416, 420, 422, 430, 426, 427, 425, 441, 445, 437, 439, 435, 179, 163, 167, 175, 173, 172, 188, 190, 254, 255, 247, 245, 229, 228, 230, 226, 234, 235, 233, 249, 248, 240, 176, 48, 56, 57, 41, 43, 42, 46, 38, 36, 37, 53, 55, 63, 319, 303, 301, 300, 316, 308, 310, 306, 290, 291, 289, 305, 369, 373, 357, 356, 358, 366, 382, 350, 94, 95, 87, 85, 81, 89, 73, 75, 74, 66, 70, 68, 76, 332]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (7 : Vertex), (8 : Vertex), (13 : Vertex), (15 : Vertex), (18 : Vertex), (19 : Vertex), (20 : Vertex), (22 : Vertex), (26 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (128 : Vertex), (129 : Vertex), (130 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (142 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (157 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (195 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (206 : Vertex), (207 : Vertex), (210 : Vertex), (211 : Vertex), (212 : Vertex), (214 : Vertex), (218 : Vertex), (219 : Vertex), (220 : Vertex), (221 : Vertex), (256 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (275 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (285 : Vertex), (320 : Vertex), (321 : Vertex), (323 : Vertex), (327 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (338 : Vertex), (339 : Vertex), (340 : Vertex), (344 : Vertex), (349 : Vertex), (385 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (391 : Vertex), (392 : Vertex), (396 : Vertex), (397 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (404 : Vertex), (406 : Vertex), (408 : Vertex), (410 : Vertex), (411 : Vertex), (412 : Vertex), (414 : Vertex), (415 : Vertex), (450 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (477 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (8 : Vertex), (13 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (128 : Vertex), (133 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (206 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (256 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (279 : Vertex), (280 : Vertex), (283 : Vertex), (285 : Vertex), (321 : Vertex), (327 : Vertex), (333 : Vertex), (336 : Vertex), (339 : Vertex), (385 : Vertex), (386 : Vertex), (391 : Vertex), (392 : Vertex), (397 : Vertex), (400 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (415 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (465 : Vertex), (471 : Vertex), (472 : Vertex), (477 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (15 : Vertex), (18 : Vertex), (20 : Vertex), (27 : Vertex), (29 : Vertex), (129 : Vertex), (130 : Vertex), (132 : Vertex), (136 : Vertex), (139 : Vertex), (142 : Vertex), (149 : Vertex), (150 : Vertex), (153 : Vertex), (154 : Vertex), (159 : Vertex), (192 : Vertex), (195 : Vertex), (207 : Vertex), (210 : Vertex), (212 : Vertex), (219 : Vertex), (221 : Vertex), (260 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (275 : Vertex), (277 : Vertex), (281 : Vertex), (282 : Vertex), (320 : Vertex), (323 : Vertex), (332 : Vertex), (335 : Vertex), (338 : Vertex), (340 : Vertex), (344 : Vertex), (349 : Vertex), (387 : Vertex), (389 : Vertex), (396 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (404 : Vertex), (408 : Vertex), (411 : Vertex), (414 : Vertex), (450 : Vertex), (452 : Vertex), (456 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (469 : Vertex), (473 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (7 : Vertex), (8 : Vertex), (13 : Vertex), (15 : Vertex), (18 : Vertex), (19 : Vertex), (20 : Vertex), (22 : Vertex), (26 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (128 : Vertex), (129 : Vertex), (130 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (142 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (157 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (195 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (206 : Vertex), (207 : Vertex), (210 : Vertex), (211 : Vertex), (212 : Vertex), (214 : Vertex), (218 : Vertex), (219 : Vertex), (220 : Vertex), (221 : Vertex), (256 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (275 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (285 : Vertex), (320 : Vertex), (321 : Vertex), (323 : Vertex), (327 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (338 : Vertex), (339 : Vertex), (340 : Vertex), (344 : Vertex), (349 : Vertex), (385 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (391 : Vertex), (392 : Vertex), (396 : Vertex), (397 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (404 : Vertex), (406 : Vertex), (408 : Vertex), (410 : Vertex), (411 : Vertex), (412 : Vertex), (414 : Vertex), (415 : Vertex), (450 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (477 : Vertex), (479 : Vertex)]
def head : Vertex := 332
def ban : Nat := 13407807927946761049352202438106755253046442465882716429615957342472708446636835456465306734246478674714955845191276722652262138237567597423268690772844148
def reachable : Nat := 1995836050221822560099090874432923354709676948107604101249055583436711520336567563920424752975076012995209328201491744574378972523164958233239947
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
theorem evenSide_length : evenSide.length = 63 := by decide

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

end Snake9.Regrowth.E112005
