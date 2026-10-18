import RegrowthParityCounts
namespace Snake9.Regrowth.E112106
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 16, 18, 22, 30, 28, 29, 13, 9, 265, 281, 283, 282, 266, 270, 268, 260, 276, 277, 279, 263, 327, 335, 333, 349, 348, 350, 342, 338, 339, 337, 321, 320, 328, 456, 200, 192, 193, 209, 211, 210, 218, 222, 220, 221, 205, 207, 199, 198, 454, 486, 502, 510, 508, 509, 493, 489, 425, 441, 443, 442, 426, 430, 428, 420, 436, 437, 439, 423, 167, 175, 173, 189, 188, 190, 182, 178, 179, 177, 161, 160, 168, 40, 104, 96, 97, 113, 115, 114, 122, 126, 124, 125, 109, 111, 103, 102, 38, 36, 52, 53, 55, 63, 59, 43, 299, 303, 301, 293, 289, 305, 307]
def region : List Vertex := [(3 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (74 : Vertex), (75 : Vertex), (76 : Vertex), (78 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (91 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (142 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (159 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (240 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (255 : Vertex), (290 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (312 : Vertex), (316 : Vertex), (318 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (362 : Vertex), (364 : Vertex), (366 : Vertex), (368 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (376 : Vertex), (377 : Vertex), (379 : Vertex), (383 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (395 : Vertex), (397 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (408 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (415 : Vertex), (451 : Vertex), (453 : Vertex), (459 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex), (480 : Vertex), (483 : Vertex), (496 : Vertex), (497 : Vertex), (499 : Vertex)]
def oddSide : List Vertex := [(67 : Vertex), (69 : Vertex), (74 : Vertex), (76 : Vertex), (84 : Vertex), (87 : Vertex), (88 : Vertex), (91 : Vertex), (131 : Vertex), (133 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (155 : Vertex), (227 : Vertex), (229 : Vertex), (234 : Vertex), (236 : Vertex), (244 : Vertex), (247 : Vertex), (248 : Vertex), (251 : Vertex), (290 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (355 : Vertex), (362 : Vertex), (364 : Vertex), (372 : Vertex), (375 : Vertex), (376 : Vertex), (379 : Vertex), (385 : Vertex), (386 : Vertex), (395 : Vertex), (397 : Vertex), (400 : Vertex), (403 : Vertex), (406 : Vertex), (412 : Vertex), (415 : Vertex), (451 : Vertex), (453 : Vertex), (468 : Vertex), (471 : Vertex), (475 : Vertex), (496 : Vertex), (499 : Vertex)]
def evenSide : List Vertex := [(3 : Vertex), (66 : Vertex), (68 : Vertex), (75 : Vertex), (78 : Vertex), (85 : Vertex), (89 : Vertex), (95 : Vertex), (130 : Vertex), (132 : Vertex), (139 : Vertex), (142 : Vertex), (149 : Vertex), (153 : Vertex), (159 : Vertex), (226 : Vertex), (228 : Vertex), (235 : Vertex), (238 : Vertex), (240 : Vertex), (245 : Vertex), (249 : Vertex), (255 : Vertex), (306 : Vertex), (312 : Vertex), (318 : Vertex), (354 : Vertex), (356 : Vertex), (366 : Vertex), (368 : Vertex), (373 : Vertex), (377 : Vertex), (383 : Vertex), (384 : Vertex), (387 : Vertex), (389 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (408 : Vertex), (413 : Vertex), (414 : Vertex), (459 : Vertex), (464 : Vertex), (469 : Vertex), (473 : Vertex), (479 : Vertex), (480 : Vertex), (483 : Vertex), (497 : Vertex)]
def others : List Vertex := [(3 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (74 : Vertex), (75 : Vertex), (76 : Vertex), (78 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (91 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (142 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (159 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (240 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (255 : Vertex), (290 : Vertex), (306 : Vertex), (310 : Vertex), (312 : Vertex), (316 : Vertex), (318 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (362 : Vertex), (364 : Vertex), (366 : Vertex), (368 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (376 : Vertex), (377 : Vertex), (379 : Vertex), (383 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (395 : Vertex), (397 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (408 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (415 : Vertex), (451 : Vertex), (453 : Vertex), (459 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex), (480 : Vertex), (483 : Vertex), (496 : Vertex), (497 : Vertex), (499 : Vertex)]
def head : Vertex := 307
def ban : Nat := 13405557444112681217484017626146362012698480866030157325160546434139923074672558413655005090742243051712235311052505904763703951870241736246187600264560631
def reachable : Nat := 2250485829915882090007372059484114780884954562236052563015009581840955400988563146869207424660375977796547133980146090049930941704833700246048741523464
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

end Snake9.Regrowth.E112106
