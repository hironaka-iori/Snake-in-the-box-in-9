import RegrowthParityCounts
namespace Snake9.Regrowth.E112136
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 17, 19, 18, 22, 6, 70, 68, 69, 85, 87, 95, 91, 75, 11, 15, 13, 29, 28, 24, 280, 281, 283, 287, 279, 277, 276, 260, 268, 270, 266, 258, 259, 387, 451, 450, 458, 462, 460, 452, 453, 469, 471, 479, 475, 473, 472, 464, 400, 432, 436, 437, 439, 447, 443, 427, 171, 175, 173, 165, 161, 177, 179, 178, 182, 190, 188, 184, 248, 249, 251, 255, 247, 245, 244, 228, 236, 238, 234, 226, 227, 99, 355, 354, 362, 366, 364, 356, 357, 373, 375, 383, 379, 377, 376, 368, 112, 114, 118, 126, 124, 125, 109, 105, 41, 57, 59, 58, 42, 46, 44]
def region : List Vertex := [(36 : Vertex), (39 : Vertex), (44 : Vertex), (52 : Vertex), (53 : Vertex), (55 : Vertex), (72 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (142 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (320 : Vertex), (321 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (390 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (418 : Vertex), (422 : Vertex), (424 : Vertex), (428 : Vertex), (430 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(44 : Vertex), (52 : Vertex), (55 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (155 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (289 : Vertex), (295 : Vertex), (296 : Vertex), (301 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (321 : Vertex), (327 : Vertex), (328 : Vertex), (333 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (392 : Vertex), (397 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (422 : Vertex), (428 : Vertex), (481 : Vertex), (487 : Vertex), (488 : Vertex), (493 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(36 : Vertex), (39 : Vertex), (53 : Vertex), (72 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (136 : Vertex), (142 : Vertex), (149 : Vertex), (153 : Vertex), (154 : Vertex), (159 : Vertex), (192 : Vertex), (201 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (221 : Vertex), (222 : Vertex), (288 : Vertex), (294 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (317 : Vertex), (318 : Vertex), (320 : Vertex), (329 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (349 : Vertex), (350 : Vertex), (390 : Vertex), (393 : Vertex), (399 : Vertex), (413 : Vertex), (414 : Vertex), (418 : Vertex), (424 : Vertex), (430 : Vertex), (480 : Vertex), (486 : Vertex), (489 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(36 : Vertex), (39 : Vertex), (52 : Vertex), (53 : Vertex), (55 : Vertex), (72 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (142 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (320 : Vertex), (321 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (390 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (418 : Vertex), (422 : Vertex), (424 : Vertex), (428 : Vertex), (430 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 44
def ban : Nat := 7316306309409389199870910889676529606769722530846273387150721713855687621440045449359657325897219233092718158988581654899937892674889081396176826130235391
def reachable : Nat := 6091501620533207899703114108529316520709643289746119990572839729866076408633501527442216972269684194597313699197904395953815990137057488550256822875848704
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
theorem oddSide_length : oddSide.length = 47 := by decide
theorem evenSide_length : evenSide.length = 50 := by decide

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

end Snake9.Regrowth.E112136
