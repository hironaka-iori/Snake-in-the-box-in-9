import RegrowthParityCounts
namespace Snake9.Regrowth.E112182
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 17, 19, 18, 22, 6, 262, 326, 327, 335, 333, 329, 321, 337, 339, 338, 346, 350, 348, 340, 276, 277, 279, 287, 283, 267, 11, 15, 13, 29, 28, 24, 88, 89, 91, 95, 87, 85, 69, 68, 76, 78, 74, 66, 67, 195, 451, 450, 458, 462, 460, 452, 453, 469, 471, 479, 475, 473, 472, 464, 208, 240, 244, 245, 247, 255, 251, 235, 171, 175, 173, 165, 161, 177, 179, 178, 182, 190, 188, 184, 440, 441, 443, 447, 439, 437, 436, 420, 428, 430, 426, 418, 419, 291, 355, 354, 362, 366, 364, 356, 357, 373, 375, 383, 379, 377, 376, 368, 304, 306, 310]
def region : List Vertex := [(34 : Vertex), (36 : Vertex), (39 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (44 : Vertex), (46 : Vertex), (52 : Vertex), (53 : Vertex), (55 : Vertex), (57 : Vertex), (58 : Vertex), (59 : Vertex), (63 : Vertex), (96 : Vertex), (97 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (109 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (142 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (198 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (226 : Vertex), (230 : Vertex), (232 : Vertex), (236 : Vertex), (238 : Vertex), (264 : Vertex), (268 : Vertex), (296 : Vertex), (297 : Vertex), (301 : Vertex), (303 : Vertex), (310 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (384 : Vertex), (385 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(41 : Vertex), (42 : Vertex), (44 : Vertex), (52 : Vertex), (55 : Vertex), (59 : Vertex), (97 : Vertex), (103 : Vertex), (104 : Vertex), (109 : Vertex), (115 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (155 : Vertex), (200 : Vertex), (205 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (230 : Vertex), (236 : Vertex), (268 : Vertex), (296 : Vertex), (301 : Vertex), (310 : Vertex), (316 : Vertex), (385 : Vertex), (391 : Vertex), (392 : Vertex), (397 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (481 : Vertex), (487 : Vertex), (488 : Vertex), (493 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(34 : Vertex), (36 : Vertex), (39 : Vertex), (40 : Vertex), (46 : Vertex), (53 : Vertex), (57 : Vertex), (58 : Vertex), (63 : Vertex), (96 : Vertex), (102 : Vertex), (105 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (125 : Vertex), (126 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (136 : Vertex), (142 : Vertex), (149 : Vertex), (153 : Vertex), (154 : Vertex), (159 : Vertex), (198 : Vertex), (201 : Vertex), (207 : Vertex), (221 : Vertex), (222 : Vertex), (226 : Vertex), (232 : Vertex), (238 : Vertex), (264 : Vertex), (297 : Vertex), (303 : Vertex), (317 : Vertex), (318 : Vertex), (384 : Vertex), (393 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (413 : Vertex), (414 : Vertex), (480 : Vertex), (486 : Vertex), (489 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(34 : Vertex), (36 : Vertex), (39 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (44 : Vertex), (46 : Vertex), (52 : Vertex), (53 : Vertex), (55 : Vertex), (57 : Vertex), (58 : Vertex), (59 : Vertex), (63 : Vertex), (96 : Vertex), (97 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (109 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (142 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (198 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (226 : Vertex), (230 : Vertex), (232 : Vertex), (236 : Vertex), (238 : Vertex), (264 : Vertex), (268 : Vertex), (296 : Vertex), (297 : Vertex), (301 : Vertex), (303 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (384 : Vertex), (385 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (397 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 310
def ban : Nat := 7316306309409389199870914410344237378988449163457149559791792408140310342548536251387297950704222306373709340636979067733783582399540099158693542080020479
def reachable : Nat := 6091501620533207899703110587861608748490916657135243817931769035581453687525010725414576347462681121316322517549506983119970300412406470787740106926063616
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
theorem oddSide_length : oddSide.length = 48 := by decide
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

end Snake9.Regrowth.E112182
