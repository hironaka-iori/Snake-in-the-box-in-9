import RegrowthParityCounts
namespace Snake9.Regrowth.E112211
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[472, 473, 475, 479, 471, 469, 453, 452, 460, 462, 458, 450, 451, 195, 67, 66, 74, 78, 76, 68, 69, 85, 87, 95, 91, 89, 88, 80, 208, 240, 244, 245, 247, 255, 251, 235, 171, 175, 173, 165, 161, 177, 179, 178, 182, 190, 188, 184, 440, 441, 443, 447, 439, 437, 436, 420, 428, 430, 426, 418, 419, 291, 355, 354, 362, 366, 364, 356, 357, 373, 375, 383, 379, 377, 376, 368, 304, 306, 310, 318, 316, 317, 301, 297, 41, 57, 59, 58, 42, 46, 44, 36, 52, 53, 55, 39, 103, 111, 109, 125, 124, 126, 118, 114, 115, 113, 97, 96, 104, 232, 488, 480]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (8 : Vertex), (11 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (128 : Vertex), (130 : Vertex), (132 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (142 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (157 : Vertex), (159 : Vertex), (198 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (226 : Vertex), (230 : Vertex), (238 : Vertex), (256 : Vertex), (257 : Vertex), (258 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (270 : Vertex), (271 : Vertex), (273 : Vertex), (275 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (331 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (340 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (385 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (395 : Vertex), (397 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (8 : Vertex), (11 : Vertex), (13 : Vertex), (19 : Vertex), (22 : Vertex), (28 : Vertex), (128 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (155 : Vertex), (157 : Vertex), (205 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (230 : Vertex), (256 : Vertex), (261 : Vertex), (262 : Vertex), (266 : Vertex), (268 : Vertex), (271 : Vertex), (273 : Vertex), (276 : Vertex), (279 : Vertex), (280 : Vertex), (283 : Vertex), (321 : Vertex), (327 : Vertex), (328 : Vertex), (331 : Vertex), (333 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (385 : Vertex), (391 : Vertex), (392 : Vertex), (395 : Vertex), (397 : Vertex), (400 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (481 : Vertex), (487 : Vertex), (493 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (29 : Vertex), (30 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (136 : Vertex), (142 : Vertex), (149 : Vertex), (153 : Vertex), (154 : Vertex), (159 : Vertex), (198 : Vertex), (201 : Vertex), (207 : Vertex), (221 : Vertex), (222 : Vertex), (226 : Vertex), (238 : Vertex), (257 : Vertex), (258 : Vertex), (260 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (270 : Vertex), (275 : Vertex), (277 : Vertex), (281 : Vertex), (282 : Vertex), (287 : Vertex), (320 : Vertex), (326 : Vertex), (329 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (340 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (390 : Vertex), (393 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (413 : Vertex), (414 : Vertex), (480 : Vertex), (486 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (8 : Vertex), (11 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (128 : Vertex), (130 : Vertex), (132 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (142 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (157 : Vertex), (159 : Vertex), (198 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (226 : Vertex), (230 : Vertex), (238 : Vertex), (256 : Vertex), (257 : Vertex), (258 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (270 : Vertex), (271 : Vertex), (273 : Vertex), (275 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (331 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (340 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (385 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (395 : Vertex), (397 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 480
def ban : Nat := 7316308710034024392868940342792504424466423110431221298239708983704196925458511245757751514521093663450824168536331490164896475544129389287583779262650044
def reachable : Nat := 6091499219908572706705084655413341703012942710161172079483852460017567104615035731044122783645809764239207689650154560688857407267817180658849869743434051
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
theorem evenSide_length : evenSide.length = 59 := by decide

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

end Snake9.Regrowth.E112211
