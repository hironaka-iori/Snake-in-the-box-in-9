import RegrowthParityCounts
namespace Snake9.Regrowth.E112116
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 16, 272, 280, 281, 283, 267, 266, 270, 268, 260, 261, 277, 279, 278, 22, 30, 28, 29, 13, 9, 73, 89, 91, 95, 87, 85, 84, 68, 76, 78, 74, 66, 67, 3, 131, 130, 138, 142, 140, 132, 148, 149, 151, 159, 155, 153, 152, 216, 220, 222, 214, 210, 211, 209, 193, 197, 205, 207, 203, 459, 475, 479, 471, 469, 468, 464, 496, 432, 440, 441, 443, 447, 439, 437, 421, 420, 428, 430, 426, 418, 419, 483, 355, 354, 362, 366, 364, 356, 372, 373, 375, 383, 379, 377, 376, 120, 124, 126, 118, 114, 115, 113, 97, 101, 109, 111, 107, 43, 59, 63, 55]
def region : List Vertex := [(34 : Vertex), (36 : Vertex), (38 : Vertex), (39 : Vertex), (40 : Vertex), (44 : Vertex), (46 : Vertex), (52 : Vertex), (53 : Vertex), (55 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (173 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (224 : Vertex), (226 : Vertex), (228 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (238 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (253 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (314 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (385 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (454 : Vertex), (456 : Vertex), (460 : Vertex), (462 : Vertex), (486 : Vertex), (488 : Vertex), (489 : Vertex), (493 : Vertex), (495 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(38 : Vertex), (44 : Vertex), (52 : Vertex), (55 : Vertex), (161 : Vertex), (167 : Vertex), (168 : Vertex), (173 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (224 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (244 : Vertex), (247 : Vertex), (251 : Vertex), (253 : Vertex), (289 : Vertex), (295 : Vertex), (296 : Vertex), (301 : Vertex), (307 : Vertex), (314 : Vertex), (316 : Vertex), (321 : Vertex), (327 : Vertex), (328 : Vertex), (333 : Vertex), (339 : Vertex), (346 : Vertex), (348 : Vertex), (385 : Vertex), (391 : Vertex), (392 : Vertex), (397 : Vertex), (403 : Vertex), (410 : Vertex), (412 : Vertex), (454 : Vertex), (460 : Vertex), (488 : Vertex), (493 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(34 : Vertex), (36 : Vertex), (39 : Vertex), (40 : Vertex), (46 : Vertex), (53 : Vertex), (160 : Vertex), (166 : Vertex), (169 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (189 : Vertex), (190 : Vertex), (226 : Vertex), (228 : Vertex), (231 : Vertex), (232 : Vertex), (238 : Vertex), (245 : Vertex), (249 : Vertex), (250 : Vertex), (255 : Vertex), (288 : Vertex), (294 : Vertex), (297 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (317 : Vertex), (318 : Vertex), (320 : Vertex), (326 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (390 : Vertex), (393 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (456 : Vertex), (462 : Vertex), (486 : Vertex), (489 : Vertex), (495 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(34 : Vertex), (36 : Vertex), (38 : Vertex), (39 : Vertex), (40 : Vertex), (44 : Vertex), (46 : Vertex), (52 : Vertex), (53 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (173 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (224 : Vertex), (226 : Vertex), (228 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (238 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (253 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (314 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (385 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (454 : Vertex), (456 : Vertex), (460 : Vertex), (462 : Vertex), (486 : Vertex), (488 : Vertex), (489 : Vertex), (493 : Vertex), (495 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 55
def ban : Nat := 7319170935140343294249338016512612904489394641843793532208568552118036625631666743179603088083352537406057964342373883138497318562615531097768574331125759
def reachable : Nat := 6088636994802253805324686981693233222989971178748599845514992891603727404441880233622271210083550890283973893844112167715256564249331038848665074674958336
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

end Snake9.Regrowth.E112116
