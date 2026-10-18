import RegrowthParityCounts
namespace Snake9.Regrowth.E112235
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[376, 377, 379, 383, 375, 373, 372, 356, 364, 366, 362, 354, 355, 99, 227, 226, 234, 238, 236, 228, 244, 245, 247, 255, 251, 249, 248, 184, 188, 190, 182, 178, 179, 177, 161, 165, 173, 175, 171, 427, 443, 447, 439, 437, 436, 432, 400, 464, 472, 473, 475, 479, 471, 469, 453, 452, 460, 462, 458, 450, 451, 387, 259, 258, 266, 270, 268, 260, 261, 277, 279, 287, 283, 281, 280, 24, 28, 29, 13, 15, 11, 75, 91, 95, 87, 85, 84, 80, 112, 114, 118, 126, 124, 125, 109, 105, 41, 57, 59, 58, 42, 46, 44, 36, 52, 53, 55, 39, 295, 303, 301, 317]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (65 : Vertex), (66 : Vertex), (70 : Vertex), (72 : Vertex), (76 : Vertex), (78 : Vertex), (128 : Vertex), (130 : Vertex), (132 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (142 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (288 : Vertex), (289 : Vertex), (296 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (390 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (418 : Vertex), (422 : Vertex), (424 : Vertex), (428 : Vertex), (430 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (19 : Vertex), (22 : Vertex), (70 : Vertex), (76 : Vertex), (128 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (155 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (289 : Vertex), (296 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (321 : Vertex), (327 : Vertex), (328 : Vertex), (333 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (392 : Vertex), (397 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (422 : Vertex), (428 : Vertex), (481 : Vertex), (487 : Vertex), (488 : Vertex), (493 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (17 : Vertex), (18 : Vertex), (65 : Vertex), (66 : Vertex), (72 : Vertex), (78 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (136 : Vertex), (142 : Vertex), (149 : Vertex), (153 : Vertex), (154 : Vertex), (159 : Vertex), (192 : Vertex), (198 : Vertex), (201 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (221 : Vertex), (222 : Vertex), (288 : Vertex), (305 : Vertex), (306 : Vertex), (317 : Vertex), (318 : Vertex), (320 : Vertex), (326 : Vertex), (329 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (349 : Vertex), (350 : Vertex), (390 : Vertex), (393 : Vertex), (399 : Vertex), (413 : Vertex), (414 : Vertex), (418 : Vertex), (424 : Vertex), (430 : Vertex), (480 : Vertex), (486 : Vertex), (489 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (65 : Vertex), (66 : Vertex), (70 : Vertex), (72 : Vertex), (76 : Vertex), (78 : Vertex), (128 : Vertex), (130 : Vertex), (132 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (142 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (288 : Vertex), (289 : Vertex), (296 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (318 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (390 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (418 : Vertex), (422 : Vertex), (424 : Vertex), (428 : Vertex), (430 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 317
def ban : Nat := 7316306309409389199870910889676529606769722530846273387014285562402085314662603335856367460314540959030093733351760031433332033146815536684130312706457532
def reachable : Nat := 6091501620533207899703114108529316520709643289746119990709275881319678715410943640945506837852362468659938124834726019420421849665131033262303336299626563
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
theorem oddSide_length : oddSide.length = 49 := by decide
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

end Snake9.Regrowth.E112235
