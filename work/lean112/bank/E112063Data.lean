import RegrowthParityCounts
namespace Snake9.Regrowth.E112063
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[280, 281, 265, 267, 266, 258, 262, 260, 261, 277, 279, 287, 286, 350, 382, 366, 358, 356, 357, 373, 369, 113, 97, 99, 98, 114, 118, 116, 124, 108, 109, 111, 127, 63, 55, 53, 37, 36, 38, 46, 42, 43, 41, 57, 56, 48, 176, 432, 440, 441, 425, 427, 426, 418, 422, 420, 421, 437, 439, 447, 446, 190, 188, 172, 173, 175, 167, 163, 179, 243, 247, 245, 253, 249, 233, 235, 234, 238, 230, 228, 224, 480, 481, 483, 487, 495, 493, 492, 508, 500, 502, 498, 506, 507, 379, 315, 314, 306, 310, 308, 316, 317, 301, 303, 295, 291, 289, 288, 296, 360, 328, 332]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (7 : Vertex), (8 : Vertex), (12 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (20 : Vertex), (22 : Vertex), (26 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (64 : Vertex), (68 : Vertex), (69 : Vertex), (70 : Vertex), (71 : Vertex), (73 : Vertex), (74 : Vertex), (75 : Vertex), (78 : Vertex), (80 : Vertex), (83 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (90 : Vertex), (91 : Vertex), (93 : Vertex), (128 : Vertex), (129 : Vertex), (130 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (142 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (157 : Vertex), (159 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (199 : Vertex), (200 : Vertex), (204 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex), (214 : Vertex), (216 : Vertex), (218 : Vertex), (219 : Vertex), (220 : Vertex), (222 : Vertex), (223 : Vertex), (321 : Vertex), (323 : Vertex), (327 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (338 : Vertex), (339 : Vertex), (340 : Vertex), (349 : Vertex), (384 : Vertex), (385 : Vertex), (387 : Vertex), (391 : Vertex), (392 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (404 : Vertex), (406 : Vertex), (410 : Vertex), (411 : Vertex), (412 : Vertex), (413 : Vertex), (450 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (477 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (8 : Vertex), (13 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (64 : Vertex), (69 : Vertex), (70 : Vertex), (73 : Vertex), (74 : Vertex), (87 : Vertex), (88 : Vertex), (91 : Vertex), (93 : Vertex), (128 : Vertex), (133 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex), (193 : Vertex), (194 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (208 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (223 : Vertex), (321 : Vertex), (327 : Vertex), (333 : Vertex), (336 : Vertex), (339 : Vertex), (385 : Vertex), (391 : Vertex), (392 : Vertex), (397 : Vertex), (398 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (465 : Vertex), (471 : Vertex), (472 : Vertex), (477 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (12 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (20 : Vertex), (27 : Vertex), (29 : Vertex), (68 : Vertex), (71 : Vertex), (75 : Vertex), (78 : Vertex), (80 : Vertex), (83 : Vertex), (85 : Vertex), (89 : Vertex), (90 : Vertex), (129 : Vertex), (130 : Vertex), (132 : Vertex), (136 : Vertex), (139 : Vertex), (142 : Vertex), (149 : Vertex), (150 : Vertex), (153 : Vertex), (154 : Vertex), (159 : Vertex), (195 : Vertex), (197 : Vertex), (204 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex), (216 : Vertex), (219 : Vertex), (222 : Vertex), (323 : Vertex), (332 : Vertex), (335 : Vertex), (338 : Vertex), (340 : Vertex), (349 : Vertex), (384 : Vertex), (387 : Vertex), (396 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (404 : Vertex), (411 : Vertex), (413 : Vertex), (450 : Vertex), (452 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (469 : Vertex), (473 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (7 : Vertex), (8 : Vertex), (12 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (20 : Vertex), (22 : Vertex), (26 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (64 : Vertex), (68 : Vertex), (69 : Vertex), (70 : Vertex), (71 : Vertex), (73 : Vertex), (74 : Vertex), (75 : Vertex), (78 : Vertex), (80 : Vertex), (83 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (90 : Vertex), (91 : Vertex), (93 : Vertex), (128 : Vertex), (129 : Vertex), (130 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (142 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (157 : Vertex), (159 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (199 : Vertex), (200 : Vertex), (204 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex), (214 : Vertex), (216 : Vertex), (218 : Vertex), (219 : Vertex), (220 : Vertex), (222 : Vertex), (223 : Vertex), (321 : Vertex), (323 : Vertex), (327 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (338 : Vertex), (339 : Vertex), (340 : Vertex), (349 : Vertex), (384 : Vertex), (385 : Vertex), (387 : Vertex), (391 : Vertex), (392 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (404 : Vertex), (406 : Vertex), (410 : Vertex), (411 : Vertex), (412 : Vertex), (413 : Vertex), (450 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (477 : Vertex), (479 : Vertex)]
def head : Vertex := 332
def ban : Nat := 13407807927946761235422915857888530524716021396429703191675202029410825044897883301323684231939800913540372274872438602650173086131401296713189369395105396
def reachable : Nat := 1995835864151109140317315602763344424162690186048359414310938985175663675478190066227102514149659583314047448203580796680545273233244279610978699
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

end Snake9.Regrowth.E112063
