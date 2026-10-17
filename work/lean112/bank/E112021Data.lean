import RegrowthParityCounts
namespace Snake9.Regrowth.E112021
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[361, 360, 362, 366, 358, 356, 372, 373, 381, 383, 379, 371, 370, 498, 434, 435, 443, 447, 445, 437, 436, 420, 422, 430, 426, 424, 425, 417, 481, 483, 487, 495, 493, 492, 508, 504, 248, 232, 234, 235, 251, 255, 253, 245, 229, 228, 230, 246, 182, 190, 188, 172, 173, 175, 167, 163, 162, 160, 176, 177, 185, 57, 121, 113, 112, 96, 98, 99, 103, 111, 109, 108, 124, 126, 122, 58, 42, 46, 38, 36, 37, 293, 301, 303, 299, 291, 290, 288, 304, 312, 316, 318, 310, 311, 55, 23, 7, 15, 13, 12, 28, 24, 88, 72, 74, 75, 91, 95, 93, 85, 69, 68]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (2 : Vertex), (17 : Vertex), (18 : Vertex), (68 : Vertex), (70 : Vertex), (82 : Vertex), (86 : Vertex), (129 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (142 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (154 : Vertex), (155 : Vertex), (157 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (199 : Vertex), (201 : Vertex), (204 : Vertex), (205 : Vertex), (206 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (212 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (220 : Vertex), (222 : Vertex), (257 : Vertex), (260 : Vertex), (262 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (270 : Vertex), (273 : Vertex), (274 : Vertex), (275 : Vertex), (276 : Vertex), (277 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (285 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (323 : Vertex), (327 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (348 : Vertex), (350 : Vertex), (384 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (391 : Vertex), (395 : Vertex), (396 : Vertex), (397 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (414 : Vertex), (448 : Vertex), (450 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (471 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex), (478 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (2 : Vertex), (70 : Vertex), (82 : Vertex), (133 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (146 : Vertex), (148 : Vertex), (155 : Vertex), (157 : Vertex), (193 : Vertex), (194 : Vertex), (199 : Vertex), (205 : Vertex), (206 : Vertex), (208 : Vertex), (211 : Vertex), (217 : Vertex), (218 : Vertex), (220 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (273 : Vertex), (274 : Vertex), (276 : Vertex), (283 : Vertex), (285 : Vertex), (321 : Vertex), (322 : Vertex), (327 : Vertex), (333 : Vertex), (336 : Vertex), (342 : Vertex), (345 : Vertex), (346 : Vertex), (348 : Vertex), (386 : Vertex), (391 : Vertex), (395 : Vertex), (397 : Vertex), (400 : Vertex), (406 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (448 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (465 : Vertex), (468 : Vertex), (471 : Vertex), (475 : Vertex), (477 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (17 : Vertex), (18 : Vertex), (68 : Vertex), (86 : Vertex), (129 : Vertex), (132 : Vertex), (136 : Vertex), (139 : Vertex), (142 : Vertex), (147 : Vertex), (149 : Vertex), (154 : Vertex), (159 : Vertex), (192 : Vertex), (195 : Vertex), (201 : Vertex), (204 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex), (215 : Vertex), (222 : Vertex), (257 : Vertex), (260 : Vertex), (264 : Vertex), (270 : Vertex), (275 : Vertex), (277 : Vertex), (281 : Vertex), (282 : Vertex), (287 : Vertex), (320 : Vertex), (323 : Vertex), (332 : Vertex), (335 : Vertex), (337 : Vertex), (343 : Vertex), (350 : Vertex), (384 : Vertex), (387 : Vertex), (389 : Vertex), (396 : Vertex), (399 : Vertex), (401 : Vertex), (407 : Vertex), (408 : Vertex), (414 : Vertex), (450 : Vertex), (452 : Vertex), (456 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (469 : Vertex), (470 : Vertex), (473 : Vertex), (474 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (2 : Vertex), (17 : Vertex), (18 : Vertex), (70 : Vertex), (82 : Vertex), (86 : Vertex), (129 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (142 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (154 : Vertex), (155 : Vertex), (157 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (199 : Vertex), (201 : Vertex), (204 : Vertex), (205 : Vertex), (206 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (212 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (220 : Vertex), (222 : Vertex), (257 : Vertex), (260 : Vertex), (262 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (270 : Vertex), (273 : Vertex), (274 : Vertex), (275 : Vertex), (276 : Vertex), (277 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (285 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (323 : Vertex), (327 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (348 : Vertex), (350 : Vertex), (384 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (391 : Vertex), (395 : Vertex), (396 : Vertex), (397 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (414 : Vertex), (448 : Vertex), (450 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (471 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex), (478 : Vertex), (479 : Vertex)]
def head : Vertex := 68
def ban : Nat := 13407807927028375549814140413407550356537318934031794257099757843552384931842351621582641089942675239221819203702097244122043048564567710662045288801894392
def reachable : Nat := 2914221549759884584798295770942046886560599120623803600169379098231195355219233208224228188468212654484388806731710834247378859284388360204189703
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

end Snake9.Regrowth.E112021
