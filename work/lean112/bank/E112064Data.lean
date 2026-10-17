import RegrowthParityCounts
namespace Snake9.Regrowth.E112064
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 3, 7, 15, 13, 12, 28, 20, 22, 18, 26, 27, 155, 411, 410, 402, 406, 404, 412, 413, 397, 399, 391, 387, 385, 384, 392, 136, 168, 172, 173, 175, 167, 163, 179, 243, 247, 245, 253, 249, 233, 235, 234, 238, 230, 228, 224, 480, 481, 483, 487, 495, 493, 492, 508, 500, 502, 498, 506, 507, 379, 315, 314, 306, 310, 308, 316, 317, 301, 303, 295, 291, 289, 288, 296, 360, 362, 366, 358, 356, 357, 373, 369, 113, 97, 99, 98, 114, 118, 116, 124, 108, 109, 111, 127, 63, 55, 53, 37, 36, 38, 46, 42, 43, 41, 57, 56, 48, 176, 432, 440]
def region : List Vertex := [(68 : Vertex), (69 : Vertex), (70 : Vertex), (72 : Vertex), (73 : Vertex), (74 : Vertex), (75 : Vertex), (78 : Vertex), (80 : Vertex), (83 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (93 : Vertex), (94 : Vertex), (130 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (142 : Vertex), (145 : Vertex), (149 : Vertex), (151 : Vertex), (158 : Vertex), (182 : Vertex), (186 : Vertex), (190 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (199 : Vertex), (204 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex), (214 : Vertex), (216 : Vertex), (218 : Vertex), (220 : Vertex), (222 : Vertex), (223 : Vertex), (258 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (273 : Vertex), (275 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (286 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (323 : Vertex), (327 : Vertex), (329 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (338 : Vertex), (339 : Vertex), (340 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (351 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (427 : Vertex), (430 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (446 : Vertex), (447 : Vertex), (450 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (478 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(69 : Vertex), (70 : Vertex), (73 : Vertex), (74 : Vertex), (87 : Vertex), (88 : Vertex), (93 : Vertex), (94 : Vertex), (133 : Vertex), (134 : Vertex), (145 : Vertex), (151 : Vertex), (158 : Vertex), (182 : Vertex), (186 : Vertex), (193 : Vertex), (194 : Vertex), (199 : Vertex), (205 : Vertex), (208 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (223 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (273 : Vertex), (279 : Vertex), (280 : Vertex), (286 : Vertex), (321 : Vertex), (322 : Vertex), (327 : Vertex), (331 : Vertex), (333 : Vertex), (336 : Vertex), (339 : Vertex), (342 : Vertex), (345 : Vertex), (346 : Vertex), (348 : Vertex), (351 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (439 : Vertex), (440 : Vertex), (446 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (465 : Vertex), (471 : Vertex), (472 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(68 : Vertex), (72 : Vertex), (75 : Vertex), (78 : Vertex), (80 : Vertex), (83 : Vertex), (85 : Vertex), (89 : Vertex), (130 : Vertex), (132 : Vertex), (142 : Vertex), (149 : Vertex), (190 : Vertex), (195 : Vertex), (197 : Vertex), (204 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex), (216 : Vertex), (222 : Vertex), (258 : Vertex), (260 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (275 : Vertex), (277 : Vertex), (281 : Vertex), (287 : Vertex), (320 : Vertex), (323 : Vertex), (329 : Vertex), (332 : Vertex), (335 : Vertex), (338 : Vertex), (340 : Vertex), (343 : Vertex), (344 : Vertex), (349 : Vertex), (350 : Vertex), (418 : Vertex), (420 : Vertex), (427 : Vertex), (430 : Vertex), (437 : Vertex), (441 : Vertex), (447 : Vertex), (450 : Vertex), (452 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (469 : Vertex), (473 : Vertex), (479 : Vertex)]
def others : List Vertex := [(68 : Vertex), (69 : Vertex), (70 : Vertex), (72 : Vertex), (73 : Vertex), (74 : Vertex), (75 : Vertex), (78 : Vertex), (80 : Vertex), (83 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (93 : Vertex), (94 : Vertex), (130 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (142 : Vertex), (145 : Vertex), (149 : Vertex), (151 : Vertex), (158 : Vertex), (182 : Vertex), (186 : Vertex), (190 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (199 : Vertex), (204 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex), (214 : Vertex), (216 : Vertex), (218 : Vertex), (220 : Vertex), (222 : Vertex), (223 : Vertex), (258 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (273 : Vertex), (275 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (286 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (323 : Vertex), (327 : Vertex), (329 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (338 : Vertex), (339 : Vertex), (340 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (351 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (427 : Vertex), (430 : Vertex), (437 : Vertex), (439 : Vertex), (441 : Vertex), (446 : Vertex), (447 : Vertex), (450 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (478 : Vertex), (479 : Vertex)]
def head : Vertex := 440
def ban : Nat := 13407807927556542666080831450824329719838011708689217555438351821759185045636424672212787367186280198493991076690750094172722008363125816121648461952057343
def reachable : Nat := 2386054433493193547381516407641354111903175822285209621962578984437122304589086930980623229196040781495735956681031874448820753824785187054026752
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

end Snake9.Regrowth.E112064
