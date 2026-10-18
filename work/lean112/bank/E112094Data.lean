import RegrowthParityCounts
namespace Snake9.Regrowth.E112094
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 3, 11, 15, 31, 287, 283, 281, 273, 277, 261, 263, 262, 258, 266, 264, 268, 332, 333, 335, 331, 323, 321, 320, 336, 344, 346, 350, 342, 343, 471, 215, 214, 222, 218, 216, 208, 209, 193, 195, 203, 207, 205, 204, 196, 452, 484, 480, 481, 483, 491, 495, 511, 447, 443, 441, 433, 437, 421, 423, 422, 418, 426, 424, 428, 172, 173, 175, 171, 163, 161, 160, 176, 184, 186, 190, 182, 183, 55, 119, 118, 126, 122, 120, 112, 113, 97, 99, 107, 111, 109, 108, 100, 36, 38, 34, 42, 40, 41, 57, 61, 317, 301, 303, 302, 318, 314, 312, 304, 288, 289]
def region : List Vertex := [(18 : Vertex), (20 : Vertex), (22 : Vertex), (24 : Vertex), (26 : Vertex), (28 : Vertex), (66 : Vertex), (69 : Vertex), (70 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (74 : Vertex), (78 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (85 : Vertex), (89 : Vertex), (91 : Vertex), (92 : Vertex), (93 : Vertex), (130 : Vertex), (133 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (142 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (153 : Vertex), (155 : Vertex), (156 : Vertex), (157 : Vertex), (226 : Vertex), (229 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (238 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (245 : Vertex), (249 : Vertex), (251 : Vertex), (252 : Vertex), (253 : Vertex), (289 : Vertex), (291 : Vertex), (307 : Vertex), (354 : Vertex), (357 : Vertex), (358 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (362 : Vertex), (370 : Vertex), (371 : Vertex), (372 : Vertex), (373 : Vertex), (377 : Vertex), (379 : Vertex), (380 : Vertex), (384 : Vertex), (385 : Vertex), (387 : Vertex), (393 : Vertex), (395 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (400 : Vertex), (402 : Vertex), (403 : Vertex), (404 : Vertex), (406 : Vertex), (408 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (462 : Vertex), (466 : Vertex), (473 : Vertex), (475 : Vertex), (476 : Vertex), (477 : Vertex), (498 : Vertex), (502 : Vertex), (504 : Vertex), (506 : Vertex), (508 : Vertex)]
def oddSide : List Vertex := [(22 : Vertex), (26 : Vertex), (28 : Vertex), (69 : Vertex), (70 : Vertex), (73 : Vertex), (74 : Vertex), (82 : Vertex), (84 : Vertex), (91 : Vertex), (93 : Vertex), (133 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (146 : Vertex), (148 : Vertex), (155 : Vertex), (157 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (242 : Vertex), (244 : Vertex), (251 : Vertex), (253 : Vertex), (289 : Vertex), (307 : Vertex), (357 : Vertex), (358 : Vertex), (361 : Vertex), (362 : Vertex), (370 : Vertex), (372 : Vertex), (379 : Vertex), (385 : Vertex), (395 : Vertex), (397 : Vertex), (398 : Vertex), (400 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (457 : Vertex), (458 : Vertex), (466 : Vertex), (475 : Vertex), (477 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(18 : Vertex), (20 : Vertex), (24 : Vertex), (66 : Vertex), (71 : Vertex), (72 : Vertex), (78 : Vertex), (83 : Vertex), (85 : Vertex), (89 : Vertex), (92 : Vertex), (130 : Vertex), (135 : Vertex), (136 : Vertex), (142 : Vertex), (147 : Vertex), (149 : Vertex), (153 : Vertex), (156 : Vertex), (226 : Vertex), (231 : Vertex), (232 : Vertex), (238 : Vertex), (243 : Vertex), (245 : Vertex), (249 : Vertex), (252 : Vertex), (291 : Vertex), (354 : Vertex), (359 : Vertex), (360 : Vertex), (371 : Vertex), (373 : Vertex), (377 : Vertex), (380 : Vertex), (384 : Vertex), (387 : Vertex), (393 : Vertex), (399 : Vertex), (402 : Vertex), (404 : Vertex), (408 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (456 : Vertex), (462 : Vertex), (473 : Vertex), (476 : Vertex), (498 : Vertex), (504 : Vertex)]
def others : List Vertex := [(18 : Vertex), (20 : Vertex), (22 : Vertex), (24 : Vertex), (26 : Vertex), (28 : Vertex), (66 : Vertex), (69 : Vertex), (70 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (74 : Vertex), (78 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (85 : Vertex), (89 : Vertex), (91 : Vertex), (92 : Vertex), (93 : Vertex), (130 : Vertex), (133 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (142 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (153 : Vertex), (155 : Vertex), (156 : Vertex), (157 : Vertex), (226 : Vertex), (229 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (238 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (245 : Vertex), (249 : Vertex), (251 : Vertex), (252 : Vertex), (253 : Vertex), (291 : Vertex), (307 : Vertex), (354 : Vertex), (357 : Vertex), (358 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (362 : Vertex), (370 : Vertex), (371 : Vertex), (372 : Vertex), (373 : Vertex), (377 : Vertex), (379 : Vertex), (380 : Vertex), (384 : Vertex), (385 : Vertex), (387 : Vertex), (393 : Vertex), (395 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (400 : Vertex), (402 : Vertex), (403 : Vertex), (404 : Vertex), (406 : Vertex), (408 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (462 : Vertex), (466 : Vertex), (473 : Vertex), (475 : Vertex), (476 : Vertex), (477 : Vertex), (498 : Vertex), (502 : Vertex), (504 : Vertex), (506 : Vertex), (508 : Vertex)]
def head : Vertex := 289
def ban : Nat := 12294036774898459922032520772154289986553156442345690033448872078751585356084800591728096390094242096151243591093297351670735632323417328523181894203604991
def reachable : Nat := 1113771155044137177541504226051556140926209378246703344274689364970178673988746385073777908072661331538788267093188699183018250488529241423251754802479104
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
theorem evenSide_length : evenSide.length = 51 := by decide

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

end Snake9.Regrowth.E112094
