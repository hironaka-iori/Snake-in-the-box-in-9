import RegrowthParityCounts
namespace Snake9.Regrowth.E112098
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 3, 7, 15, 13, 12, 28, 24, 280, 264, 266, 267, 283, 287, 285, 277, 261, 260, 262, 278, 342, 350, 348, 332, 333, 335, 327, 323, 322, 320, 336, 337, 345, 473, 217, 209, 208, 192, 194, 195, 203, 207, 205, 204, 220, 222, 214, 215, 471, 503, 487, 495, 493, 492, 508, 504, 440, 424, 426, 427, 443, 447, 445, 437, 421, 420, 422, 438, 182, 190, 188, 172, 173, 175, 167, 163, 162, 160, 176, 177, 185, 57, 121, 113, 112, 96, 98, 99, 107, 111, 109, 108, 124, 126, 118, 119, 55, 53, 37, 36, 38, 46, 42, 58, 314, 318, 316, 308, 304, 288, 290]
def region : List Vertex := [(18 : Vertex), (68 : Vertex), (69 : Vertex), (70 : Vertex), (72 : Vertex), (73 : Vertex), (74 : Vertex), (78 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (85 : Vertex), (90 : Vertex), (91 : Vertex), (93 : Vertex), (95 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (142 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (154 : Vertex), (155 : Vertex), (157 : Vertex), (159 : Vertex), (225 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (238 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (245 : Vertex), (250 : Vertex), (251 : Vertex), (253 : Vertex), (255 : Vertex), (290 : Vertex), (291 : Vertex), (295 : Vertex), (297 : Vertex), (301 : Vertex), (303 : Vertex), (307 : Vertex), (353 : Vertex), (356 : Vertex), (357 : Vertex), (358 : Vertex), (360 : Vertex), (361 : Vertex), (362 : Vertex), (366 : Vertex), (370 : Vertex), (371 : Vertex), (373 : Vertex), (379 : Vertex), (381 : Vertex), (383 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (387 : Vertex), (391 : Vertex), (393 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (404 : Vertex), (410 : Vertex), (412 : Vertex), (414 : Vertex), (449 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (456 : Vertex), (458 : Vertex), (462 : Vertex), (466 : Vertex), (468 : Vertex), (474 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (497 : Vertex), (498 : Vertex)]
def oddSide : List Vertex := [(69 : Vertex), (70 : Vertex), (73 : Vertex), (74 : Vertex), (82 : Vertex), (84 : Vertex), (91 : Vertex), (93 : Vertex), (133 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (146 : Vertex), (148 : Vertex), (155 : Vertex), (157 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (242 : Vertex), (244 : Vertex), (251 : Vertex), (253 : Vertex), (290 : Vertex), (295 : Vertex), (301 : Vertex), (307 : Vertex), (357 : Vertex), (358 : Vertex), (361 : Vertex), (362 : Vertex), (370 : Vertex), (379 : Vertex), (381 : Vertex), (385 : Vertex), (386 : Vertex), (391 : Vertex), (397 : Vertex), (398 : Vertex), (400 : Vertex), (403 : Vertex), (410 : Vertex), (412 : Vertex), (453 : Vertex), (454 : Vertex), (458 : Vertex), (466 : Vertex), (468 : Vertex), (481 : Vertex), (482 : Vertex)]
def evenSide : List Vertex := [(18 : Vertex), (68 : Vertex), (72 : Vertex), (78 : Vertex), (83 : Vertex), (85 : Vertex), (90 : Vertex), (95 : Vertex), (132 : Vertex), (136 : Vertex), (142 : Vertex), (147 : Vertex), (149 : Vertex), (154 : Vertex), (159 : Vertex), (225 : Vertex), (228 : Vertex), (232 : Vertex), (238 : Vertex), (243 : Vertex), (245 : Vertex), (250 : Vertex), (255 : Vertex), (291 : Vertex), (297 : Vertex), (303 : Vertex), (353 : Vertex), (356 : Vertex), (360 : Vertex), (366 : Vertex), (371 : Vertex), (373 : Vertex), (383 : Vertex), (384 : Vertex), (387 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (404 : Vertex), (414 : Vertex), (449 : Vertex), (452 : Vertex), (456 : Vertex), (462 : Vertex), (474 : Vertex), (480 : Vertex), (497 : Vertex), (498 : Vertex)]
def others : List Vertex := [(18 : Vertex), (68 : Vertex), (69 : Vertex), (70 : Vertex), (72 : Vertex), (73 : Vertex), (74 : Vertex), (78 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (85 : Vertex), (90 : Vertex), (91 : Vertex), (93 : Vertex), (95 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (142 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (154 : Vertex), (155 : Vertex), (157 : Vertex), (159 : Vertex), (225 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (238 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (245 : Vertex), (250 : Vertex), (251 : Vertex), (253 : Vertex), (255 : Vertex), (291 : Vertex), (295 : Vertex), (297 : Vertex), (301 : Vertex), (303 : Vertex), (307 : Vertex), (353 : Vertex), (356 : Vertex), (357 : Vertex), (358 : Vertex), (360 : Vertex), (361 : Vertex), (362 : Vertex), (366 : Vertex), (370 : Vertex), (371 : Vertex), (373 : Vertex), (379 : Vertex), (381 : Vertex), (383 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (387 : Vertex), (391 : Vertex), (393 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (404 : Vertex), (410 : Vertex), (412 : Vertex), (414 : Vertex), (449 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (456 : Vertex), (458 : Vertex), (462 : Vertex), (466 : Vertex), (468 : Vertex), (474 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (497 : Vertex), (498 : Vertex)]
def head : Vertex := 290
def ban : Nat := 13406580386562653269270587788564525519131410087873916746842927581356569281881288129115436934219350882789935764923179985123438183440601890660376881382817791
def reachable : Nat := 1227543379943830303437209641320608347955732718476630880633862365194748192258847686437363947552544900096093263306065730315699371344679286056767623266304
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
theorem oddSide_length : oddSide.length = 51 := by decide
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

end Snake9.Regrowth.E112098
