import RegrowthParityCounts
namespace Snake9.Regrowth.E112061
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[217, 221, 477, 469, 468, 452, 454, 455, 463, 459, 457, 456, 472, 474, 466, 467, 211, 243, 227, 235, 233, 232, 248, 252, 188, 172, 174, 175, 191, 187, 185, 177, 161, 160, 162, 178, 434, 442, 440, 424, 425, 427, 419, 423, 422, 420, 436, 437, 445, 317, 381, 373, 372, 356, 358, 359, 367, 363, 361, 360, 376, 378, 370, 371, 307, 305, 289, 288, 290, 298, 302, 318, 62, 58, 56, 48, 52, 36, 38, 39, 35, 43, 41, 45, 109, 108, 110, 106, 98, 96, 97, 113, 121, 123, 127, 119, 118, 246, 502, 503, 511, 507, 505, 497, 496, 480, 482, 490, 494, 492, 493, 485]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (2 : Vertex), (5 : Vertex), (8 : Vertex), (10 : Vertex), (12 : Vertex), (14 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (21 : Vertex), (22 : Vertex), (23 : Vertex), (25 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (31 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (70 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (75 : Vertex), (79 : Vertex), (80 : Vertex), (82 : Vertex), (84 : Vertex), (85 : Vertex), (88 : Vertex), (90 : Vertex), (92 : Vertex), (94 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (141 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (154 : Vertex), (158 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (197 : Vertex), (202 : Vertex), (204 : Vertex), (206 : Vertex), (208 : Vertex), (222 : Vertex), (228 : Vertex), (229 : Vertex), (245 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (267 : Vertex), (268 : Vertex), (269 : Vertex), (271 : Vertex), (272 : Vertex), (274 : Vertex), (276 : Vertex), (277 : Vertex), (278 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (284 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (323 : Vertex), (325 : Vertex), (330 : Vertex), (332 : Vertex), (333 : Vertex), (334 : Vertex), (336 : Vertex), (337 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (347 : Vertex), (348 : Vertex), (350 : Vertex), (351 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (389 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (400 : Vertex), (401 : Vertex), (406 : Vertex), (407 : Vertex), (409 : Vertex), (411 : Vertex), (412 : Vertex), (414 : Vertex), (415 : Vertex), (485 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (2 : Vertex), (8 : Vertex), (14 : Vertex), (19 : Vertex), (21 : Vertex), (22 : Vertex), (25 : Vertex), (28 : Vertex), (31 : Vertex), (67 : Vertex), (69 : Vertex), (70 : Vertex), (73 : Vertex), (79 : Vertex), (82 : Vertex), (84 : Vertex), (88 : Vertex), (94 : Vertex), (131 : Vertex), (133 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (158 : Vertex), (193 : Vertex), (194 : Vertex), (206 : Vertex), (208 : Vertex), (229 : Vertex), (259 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (268 : Vertex), (271 : Vertex), (274 : Vertex), (276 : Vertex), (279 : Vertex), (280 : Vertex), (283 : Vertex), (321 : Vertex), (322 : Vertex), (333 : Vertex), (334 : Vertex), (336 : Vertex), (342 : Vertex), (345 : Vertex), (348 : Vertex), (351 : Vertex), (385 : Vertex), (386 : Vertex), (397 : Vertex), (398 : Vertex), (400 : Vertex), (406 : Vertex), (409 : Vertex), (412 : Vertex), (415 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (5 : Vertex), (10 : Vertex), (12 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (23 : Vertex), (27 : Vertex), (29 : Vertex), (68 : Vertex), (71 : Vertex), (72 : Vertex), (75 : Vertex), (80 : Vertex), (85 : Vertex), (90 : Vertex), (92 : Vertex), (132 : Vertex), (135 : Vertex), (136 : Vertex), (139 : Vertex), (141 : Vertex), (144 : Vertex), (149 : Vertex), (150 : Vertex), (154 : Vertex), (192 : Vertex), (197 : Vertex), (202 : Vertex), (204 : Vertex), (222 : Vertex), (228 : Vertex), (245 : Vertex), (260 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (269 : Vertex), (272 : Vertex), (277 : Vertex), (278 : Vertex), (281 : Vertex), (282 : Vertex), (284 : Vertex), (287 : Vertex), (320 : Vertex), (323 : Vertex), (325 : Vertex), (330 : Vertex), (332 : Vertex), (337 : Vertex), (343 : Vertex), (347 : Vertex), (350 : Vertex), (384 : Vertex), (389 : Vertex), (394 : Vertex), (396 : Vertex), (401 : Vertex), (407 : Vertex), (411 : Vertex), (414 : Vertex), (485 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (2 : Vertex), (5 : Vertex), (8 : Vertex), (10 : Vertex), (12 : Vertex), (14 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (21 : Vertex), (22 : Vertex), (23 : Vertex), (25 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (31 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (70 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (75 : Vertex), (79 : Vertex), (80 : Vertex), (82 : Vertex), (84 : Vertex), (85 : Vertex), (88 : Vertex), (90 : Vertex), (92 : Vertex), (94 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (141 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (154 : Vertex), (158 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (197 : Vertex), (202 : Vertex), (204 : Vertex), (206 : Vertex), (208 : Vertex), (222 : Vertex), (228 : Vertex), (229 : Vertex), (245 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (267 : Vertex), (268 : Vertex), (269 : Vertex), (271 : Vertex), (272 : Vertex), (274 : Vertex), (276 : Vertex), (277 : Vertex), (278 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (284 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (323 : Vertex), (325 : Vertex), (330 : Vertex), (332 : Vertex), (333 : Vertex), (334 : Vertex), (336 : Vertex), (337 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (347 : Vertex), (348 : Vertex), (350 : Vertex), (351 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (389 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (400 : Vertex), (401 : Vertex), (406 : Vertex), (407 : Vertex), (409 : Vertex), (411 : Vertex), (412 : Vertex), (414 : Vertex), (415 : Vertex)]
def head : Vertex := 485
def ban : Nat := 13407807929942597099574024998061231215938210429048213969136195509482141165213519452497932446604669490473427961170795751102422767591733158371723905774725848
def reachable : Nat := 144614911541155391544179408587365934239622864860027524303941851562233937216603897015690299751331115220213411574709743231358247
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
theorem oddSide_length : oddSide.length = 62 := by decide
theorem evenSide_length : evenSide.length = 64 := by decide

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

end Snake9.Regrowth.E112061
