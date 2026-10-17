import RegrowthParityCounts
namespace Snake9.Regrowth.E112058
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 17, 19, 18, 22, 30, 28, 29, 13, 15, 7, 71, 87, 85, 84, 68, 76, 78, 74, 90, 91, 89, 73, 329, 333, 349, 348, 350, 342, 338, 336, 272, 280, 281, 283, 287, 279, 277, 261, 260, 268, 270, 266, 258, 259, 323, 451, 450, 458, 462, 460, 452, 468, 469, 471, 479, 475, 473, 472, 216, 220, 222, 214, 210, 211, 209, 193, 197, 205, 207, 203, 139, 155, 159, 151, 149, 148, 144, 176, 432, 440, 441, 443, 447, 439, 437, 421, 420, 428, 430, 426, 418, 419, 163, 35, 34, 42, 46, 44, 36, 52, 53, 55, 63, 59, 57, 56, 120, 124, 126, 118]
def region : List Vertex := [(96 : Vertex), (97 : Vertex), (101 : Vertex), (102 : Vertex), (107 : Vertex), (109 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (118 : Vertex), (130 : Vertex), (134 : Vertex), (136 : Vertex), (140 : Vertex), (142 : Vertex), (166 : Vertex), (168 : Vertex), (169 : Vertex), (173 : Vertex), (175 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (224 : Vertex), (226 : Vertex), (228 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (238 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (253 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (299 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (352 : Vertex), (353 : Vertex), (354 : Vertex), (356 : Vertex), (357 : Vertex), (358 : Vertex), (359 : Vertex), (360 : Vertex), (362 : Vertex), (363 : Vertex), (364 : Vertex), (366 : Vertex), (367 : Vertex), (369 : Vertex), (371 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (377 : Vertex), (378 : Vertex), (379 : Vertex), (383 : Vertex), (384 : Vertex), (385 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(97 : Vertex), (107 : Vertex), (109 : Vertex), (115 : Vertex), (118 : Vertex), (134 : Vertex), (140 : Vertex), (168 : Vertex), (173 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (224 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (244 : Vertex), (247 : Vertex), (251 : Vertex), (253 : Vertex), (289 : Vertex), (295 : Vertex), (296 : Vertex), (299 : Vertex), (301 : Vertex), (307 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (352 : Vertex), (357 : Vertex), (358 : Vertex), (362 : Vertex), (364 : Vertex), (367 : Vertex), (369 : Vertex), (372 : Vertex), (375 : Vertex), (379 : Vertex), (385 : Vertex), (391 : Vertex), (392 : Vertex), (397 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (481 : Vertex), (487 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(96 : Vertex), (101 : Vertex), (102 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (130 : Vertex), (136 : Vertex), (142 : Vertex), (166 : Vertex), (169 : Vertex), (175 : Vertex), (189 : Vertex), (190 : Vertex), (226 : Vertex), (228 : Vertex), (231 : Vertex), (232 : Vertex), (238 : Vertex), (245 : Vertex), (249 : Vertex), (250 : Vertex), (255 : Vertex), (288 : Vertex), (294 : Vertex), (297 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (317 : Vertex), (318 : Vertex), (353 : Vertex), (354 : Vertex), (356 : Vertex), (359 : Vertex), (360 : Vertex), (363 : Vertex), (366 : Vertex), (371 : Vertex), (373 : Vertex), (377 : Vertex), (378 : Vertex), (383 : Vertex), (384 : Vertex), (390 : Vertex), (393 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (413 : Vertex), (414 : Vertex), (480 : Vertex), (486 : Vertex), (489 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(96 : Vertex), (97 : Vertex), (101 : Vertex), (102 : Vertex), (107 : Vertex), (109 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (130 : Vertex), (134 : Vertex), (136 : Vertex), (140 : Vertex), (142 : Vertex), (166 : Vertex), (168 : Vertex), (169 : Vertex), (173 : Vertex), (175 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (224 : Vertex), (226 : Vertex), (228 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (238 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (253 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (299 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (352 : Vertex), (353 : Vertex), (354 : Vertex), (356 : Vertex), (357 : Vertex), (358 : Vertex), (359 : Vertex), (360 : Vertex), (362 : Vertex), (363 : Vertex), (364 : Vertex), (366 : Vertex), (367 : Vertex), (369 : Vertex), (371 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (377 : Vertex), (378 : Vertex), (379 : Vertex), (383 : Vertex), (384 : Vertex), (385 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 118
def ban : Nat := 7316299916068358152718824540833110760040158443949335365198606731433486930983789834613690067379951297899966261891266665960826763415574838542994499956637695
def reachable : Nat := 6091508013874238946855200457372735367439207376643058012524954712288277099089757142188184230786952129790065596295219384892927119396371731403439149049446400
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
theorem oddSide_length : oddSide.length = 57 := by decide
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

end Snake9.Regrowth.E112058
