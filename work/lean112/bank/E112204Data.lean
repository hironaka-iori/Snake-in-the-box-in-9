import RegrowthParityCounts
namespace Snake9.Regrowth.E112204
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 17, 19, 18, 22, 30, 28, 29, 13, 15, 11, 267, 283, 287, 279, 277, 276, 272, 304, 368, 376, 377, 379, 383, 375, 373, 357, 356, 364, 366, 362, 354, 355, 291, 419, 418, 426, 430, 428, 420, 436, 437, 439, 447, 443, 441, 440, 184, 188, 190, 182, 178, 179, 177, 161, 165, 173, 175, 171, 235, 251, 255, 247, 245, 244, 228, 230, 486, 487, 495, 493, 509, 508, 510, 506, 498, 499, 497, 481, 480, 488, 232, 104, 96, 97, 113, 115, 114, 118, 126, 124, 125, 109, 111, 103, 39, 55, 53, 52, 36, 44, 46, 42, 58, 59, 57, 41, 297, 301, 317, 316]
def region : List Vertex := [(66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (70 : Vertex), (73 : Vertex), (74 : Vertex), (76 : Vertex), (78 : Vertex), (80 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (90 : Vertex), (91 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (199 : Vertex), (201 : Vertex), (202 : Vertex), (204 : Vertex), (205 : Vertex), (206 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (216 : Vertex), (217 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (262 : Vertex), (264 : Vertex), (268 : Vertex), (270 : Vertex), (294 : Vertex), (310 : Vertex), (316 : Vertex), (318 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (385 : Vertex), (389 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(67 : Vertex), (69 : Vertex), (70 : Vertex), (73 : Vertex), (74 : Vertex), (76 : Vertex), (84 : Vertex), (87 : Vertex), (88 : Vertex), (91 : Vertex), (131 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (155 : Vertex), (193 : Vertex), (194 : Vertex), (199 : Vertex), (205 : Vertex), (206 : Vertex), (208 : Vertex), (211 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (220 : Vertex), (262 : Vertex), (268 : Vertex), (310 : Vertex), (316 : Vertex), (321 : Vertex), (327 : Vertex), (328 : Vertex), (333 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (385 : Vertex), (391 : Vertex), (392 : Vertex), (397 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (468 : Vertex), (471 : Vertex), (472 : Vertex), (475 : Vertex)]
def evenSide : List Vertex := [(66 : Vertex), (68 : Vertex), (78 : Vertex), (80 : Vertex), (85 : Vertex), (89 : Vertex), (90 : Vertex), (95 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (136 : Vertex), (142 : Vertex), (144 : Vertex), (149 : Vertex), (153 : Vertex), (154 : Vertex), (159 : Vertex), (192 : Vertex), (195 : Vertex), (197 : Vertex), (201 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (216 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (264 : Vertex), (270 : Vertex), (294 : Vertex), (318 : Vertex), (320 : Vertex), (326 : Vertex), (329 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (389 : Vertex), (390 : Vertex), (393 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (452 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (469 : Vertex), (470 : Vertex), (473 : Vertex), (479 : Vertex)]
def others : List Vertex := [(66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (70 : Vertex), (73 : Vertex), (74 : Vertex), (76 : Vertex), (78 : Vertex), (80 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (90 : Vertex), (91 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (199 : Vertex), (201 : Vertex), (202 : Vertex), (204 : Vertex), (205 : Vertex), (206 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (216 : Vertex), (217 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (262 : Vertex), (264 : Vertex), (268 : Vertex), (270 : Vertex), (294 : Vertex), (310 : Vertex), (318 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (385 : Vertex), (389 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex)]
def head : Vertex := 316
def ban : Nat := 13407807928236087838402113392769207576843463144809234361673714397770862452614237060391387120977432332944535299063062313501623760929624609145764414247403519
def reachable : Nat := 1706509261171911605436638550635902675783159016049847045950901577459309916410487177189471094745496559123423737352130121882321960800669234758680576
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
theorem oddSide_length : oddSide.length = 58 := by decide
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

end Snake9.Regrowth.E112204
