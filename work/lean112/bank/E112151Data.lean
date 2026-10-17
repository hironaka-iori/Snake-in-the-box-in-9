import RegrowthParityCounts
namespace Snake9.Regrowth.E112151
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[14, 12, 13, 29, 31, 95, 94, 86, 84, 68, 69, 71, 67, 75, 74, 72, 88, 89, 81, 17, 145, 153, 152, 136, 138, 139, 143, 135, 133, 132, 148, 150, 158, 414, 398, 396, 397, 413, 405, 407, 403, 387, 386, 384, 400, 464, 468, 452, 453, 455, 463, 479, 511, 255, 254, 246, 244, 228, 229, 231, 227, 235, 234, 232, 248, 249, 241, 497, 369, 377, 376, 360, 362, 363, 367, 359, 357, 356, 372, 374, 382, 318, 302, 300, 301, 317, 309, 311, 307, 291, 290, 288, 304, 48, 52, 36, 37, 39, 47, 43, 41, 105, 97, 96, 98, 102, 110, 108, 124, 125, 117, 119]
def region : List Vertex := [(0 : Vertex), (2 : Vertex), (18 : Vertex), (26 : Vertex), (58 : Vertex), (115 : Vertex), (119 : Vertex), (122 : Vertex), (123 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (166 : Vertex), (172 : Vertex), (173 : Vertex), (174 : Vertex), (178 : Vertex), (179 : Vertex), (181 : Vertex), (183 : Vertex), (186 : Vertex), (187 : Vertex), (188 : Vertex), (189 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (198 : Vertex), (201 : Vertex), (204 : Vertex), (205 : Vertex), (206 : Vertex), (210 : Vertex), (211 : Vertex), (213 : Vertex), (215 : Vertex), (218 : Vertex), (219 : Vertex), (220 : Vertex), (221 : Vertex), (257 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (271 : Vertex), (274 : Vertex), (276 : Vertex), (278 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (284 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (326 : Vertex), (329 : Vertex), (332 : Vertex), (333 : Vertex), (334 : Vertex), (338 : Vertex), (339 : Vertex), (341 : Vertex), (343 : Vertex), (346 : Vertex), (347 : Vertex), (348 : Vertex), (349 : Vertex), (417 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (426 : Vertex), (427 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (438 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (444 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (473 : Vertex), (474 : Vertex), (480 : Vertex), (482 : Vertex), (486 : Vertex), (489 : Vertex), (492 : Vertex), (493 : Vertex), (494 : Vertex), (498 : Vertex), (506 : Vertex), (508 : Vertex)]
def oddSide : List Vertex := [(2 : Vertex), (26 : Vertex), (115 : Vertex), (122 : Vertex), (161 : Vertex), (162 : Vertex), (173 : Vertex), (174 : Vertex), (179 : Vertex), (181 : Vertex), (186 : Vertex), (188 : Vertex), (193 : Vertex), (194 : Vertex), (205 : Vertex), (206 : Vertex), (211 : Vertex), (213 : Vertex), (218 : Vertex), (220 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (271 : Vertex), (274 : Vertex), (276 : Vertex), (280 : Vertex), (283 : Vertex), (321 : Vertex), (322 : Vertex), (333 : Vertex), (334 : Vertex), (339 : Vertex), (341 : Vertex), (346 : Vertex), (348 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (440 : Vertex), (443 : Vertex), (457 : Vertex), (458 : Vertex), (482 : Vertex), (493 : Vertex), (494 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (18 : Vertex), (58 : Vertex), (119 : Vertex), (123 : Vertex), (160 : Vertex), (166 : Vertex), (172 : Vertex), (178 : Vertex), (183 : Vertex), (187 : Vertex), (189 : Vertex), (192 : Vertex), (198 : Vertex), (201 : Vertex), (204 : Vertex), (210 : Vertex), (215 : Vertex), (219 : Vertex), (221 : Vertex), (257 : Vertex), (260 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (278 : Vertex), (281 : Vertex), (282 : Vertex), (284 : Vertex), (320 : Vertex), (326 : Vertex), (329 : Vertex), (332 : Vertex), (338 : Vertex), (343 : Vertex), (347 : Vertex), (349 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex), (424 : Vertex), (427 : Vertex), (438 : Vertex), (441 : Vertex), (442 : Vertex), (444 : Vertex), (456 : Vertex), (473 : Vertex), (474 : Vertex), (480 : Vertex), (486 : Vertex), (489 : Vertex), (492 : Vertex), (498 : Vertex)]
def others : List Vertex := [(0 : Vertex), (2 : Vertex), (18 : Vertex), (26 : Vertex), (58 : Vertex), (115 : Vertex), (122 : Vertex), (123 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (166 : Vertex), (172 : Vertex), (173 : Vertex), (174 : Vertex), (178 : Vertex), (179 : Vertex), (181 : Vertex), (183 : Vertex), (186 : Vertex), (187 : Vertex), (188 : Vertex), (189 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (198 : Vertex), (201 : Vertex), (204 : Vertex), (205 : Vertex), (206 : Vertex), (210 : Vertex), (211 : Vertex), (213 : Vertex), (215 : Vertex), (218 : Vertex), (219 : Vertex), (220 : Vertex), (221 : Vertex), (257 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (271 : Vertex), (274 : Vertex), (276 : Vertex), (278 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (284 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (326 : Vertex), (329 : Vertex), (332 : Vertex), (333 : Vertex), (334 : Vertex), (338 : Vertex), (339 : Vertex), (341 : Vertex), (343 : Vertex), (346 : Vertex), (347 : Vertex), (348 : Vertex), (349 : Vertex), (417 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (426 : Vertex), (427 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (438 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (444 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (473 : Vertex), (474 : Vertex), (480 : Vertex), (482 : Vertex), (486 : Vertex), (489 : Vertex), (492 : Vertex), (493 : Vertex), (494 : Vertex), (498 : Vertex), (506 : Vertex), (508 : Vertex)]
def head : Vertex := 119
def ban : Nat := 12359413267180347987749577906357507389642044471192791891944540621228054375527988866716745173793038735425949450706314760518229568123149241275984146515886074
def reachable : Nat := 1048394662762249111824447091848338737837321349399601485779020822493709654545558110085129124373864692264082407480171290335524314688797328670449502490198021
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
theorem oddSide_length : oddSide.length = 53 := by decide
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

end Snake9.Regrowth.E112151
