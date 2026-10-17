import RegrowthParityCounts
namespace Snake9.Regrowth.E112104
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 4, 132, 140, 141, 157, 159, 158, 154, 146, 144, 145, 129, 131, 139, 203, 219, 217, 216, 200, 192, 194, 198, 214, 215, 213, 197, 453, 449, 465, 464, 466, 474, 478, 476, 412, 404, 405, 407, 403, 411, 409, 393, 392, 384, 386, 390, 398, 399, 463, 335, 334, 326, 322, 320, 328, 344, 345, 347, 339, 343, 341, 340, 84, 80, 82, 90, 94, 95, 93, 77, 73, 65, 67, 71, 7, 23, 19, 27, 25, 24, 28, 60, 316, 308, 309, 311, 307, 315, 313, 297, 296, 288, 290, 294, 302, 303, 47, 175, 174, 166, 162, 160, 168, 184, 185, 187, 179, 183, 181, 180, 244]
def region : List Vertex := [(10 : Vertex), (14 : Vertex), (33 : Vertex), (35 : Vertex), (37 : Vertex), (42 : Vertex), (48 : Vertex), (49 : Vertex), (50 : Vertex), (54 : Vertex), (58 : Vertex), (96 : Vertex), (98 : Vertex), (100 : Vertex), (101 : Vertex), (102 : Vertex), (104 : Vertex), (106 : Vertex), (107 : Vertex), (108 : Vertex), (110 : Vertex), (113 : Vertex), (115 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (120 : Vertex), (121 : Vertex), (123 : Vertex), (225 : Vertex), (227 : Vertex), (228 : Vertex), (231 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (237 : Vertex), (240 : Vertex), (241 : Vertex), (242 : Vertex), (244 : Vertex), (250 : Vertex), (252 : Vertex), (253 : Vertex), (254 : Vertex), (255 : Vertex), (257 : Vertex), (259 : Vertex), (261 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (269 : Vertex), (272 : Vertex), (273 : Vertex), (274 : Vertex), (278 : Vertex), (282 : Vertex), (285 : Vertex), (286 : Vertex), (287 : Vertex), (353 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (359 : Vertex), (362 : Vertex), (363 : Vertex), (364 : Vertex), (365 : Vertex), (368 : Vertex), (369 : Vertex), (370 : Vertex), (374 : Vertex), (378 : Vertex), (381 : Vertex), (382 : Vertex), (383 : Vertex), (417 : Vertex), (419 : Vertex), (420 : Vertex), (421 : Vertex), (423 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (438 : Vertex), (442 : Vertex), (445 : Vertex), (446 : Vertex), (447 : Vertex), (480 : Vertex), (482 : Vertex), (483 : Vertex), (484 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (494 : Vertex), (499 : Vertex), (500 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (507 : Vertex), (509 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(14 : Vertex), (35 : Vertex), (37 : Vertex), (42 : Vertex), (49 : Vertex), (50 : Vertex), (98 : Vertex), (100 : Vertex), (104 : Vertex), (107 : Vertex), (110 : Vertex), (115 : Vertex), (117 : Vertex), (118 : Vertex), (121 : Vertex), (227 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (241 : Vertex), (242 : Vertex), (244 : Vertex), (253 : Vertex), (254 : Vertex), (259 : Vertex), (261 : Vertex), (266 : Vertex), (268 : Vertex), (273 : Vertex), (274 : Vertex), (285 : Vertex), (286 : Vertex), (355 : Vertex), (357 : Vertex), (362 : Vertex), (364 : Vertex), (369 : Vertex), (370 : Vertex), (381 : Vertex), (382 : Vertex), (419 : Vertex), (421 : Vertex), (426 : Vertex), (428 : Vertex), (433 : Vertex), (434 : Vertex), (445 : Vertex), (446 : Vertex), (482 : Vertex), (484 : Vertex), (487 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex), (494 : Vertex), (499 : Vertex), (501 : Vertex), (502 : Vertex), (505 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(10 : Vertex), (33 : Vertex), (48 : Vertex), (54 : Vertex), (58 : Vertex), (96 : Vertex), (101 : Vertex), (102 : Vertex), (106 : Vertex), (108 : Vertex), (113 : Vertex), (119 : Vertex), (120 : Vertex), (123 : Vertex), (225 : Vertex), (228 : Vertex), (231 : Vertex), (237 : Vertex), (240 : Vertex), (250 : Vertex), (252 : Vertex), (255 : Vertex), (257 : Vertex), (267 : Vertex), (269 : Vertex), (272 : Vertex), (278 : Vertex), (282 : Vertex), (287 : Vertex), (353 : Vertex), (356 : Vertex), (359 : Vertex), (363 : Vertex), (365 : Vertex), (368 : Vertex), (374 : Vertex), (378 : Vertex), (383 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex), (427 : Vertex), (429 : Vertex), (432 : Vertex), (438 : Vertex), (442 : Vertex), (447 : Vertex), (480 : Vertex), (483 : Vertex), (486 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex), (500 : Vertex), (503 : Vertex), (504 : Vertex), (507 : Vertex), (509 : Vertex)]
def others : List Vertex := [(10 : Vertex), (14 : Vertex), (33 : Vertex), (35 : Vertex), (37 : Vertex), (42 : Vertex), (48 : Vertex), (49 : Vertex), (50 : Vertex), (54 : Vertex), (58 : Vertex), (96 : Vertex), (98 : Vertex), (100 : Vertex), (101 : Vertex), (102 : Vertex), (104 : Vertex), (106 : Vertex), (107 : Vertex), (108 : Vertex), (110 : Vertex), (113 : Vertex), (115 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (120 : Vertex), (121 : Vertex), (123 : Vertex), (225 : Vertex), (227 : Vertex), (228 : Vertex), (231 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (237 : Vertex), (240 : Vertex), (241 : Vertex), (242 : Vertex), (250 : Vertex), (252 : Vertex), (253 : Vertex), (254 : Vertex), (255 : Vertex), (257 : Vertex), (259 : Vertex), (261 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (269 : Vertex), (272 : Vertex), (273 : Vertex), (274 : Vertex), (278 : Vertex), (282 : Vertex), (285 : Vertex), (286 : Vertex), (287 : Vertex), (353 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (359 : Vertex), (362 : Vertex), (363 : Vertex), (364 : Vertex), (365 : Vertex), (368 : Vertex), (369 : Vertex), (370 : Vertex), (374 : Vertex), (378 : Vertex), (381 : Vertex), (382 : Vertex), (383 : Vertex), (417 : Vertex), (419 : Vertex), (420 : Vertex), (421 : Vertex), (423 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (438 : Vertex), (442 : Vertex), (445 : Vertex), (446 : Vertex), (447 : Vertex), (480 : Vertex), (482 : Vertex), (483 : Vertex), (484 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (494 : Vertex), (499 : Vertex), (500 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (507 : Vertex), (509 : Vertex), (511 : Vertex)]
def head : Vertex := 244
def ban : Nat := 4400971488121065250210892925688999793911433992058082874381925565203619872194177537365862831221513357325169130943328755173751181511335322036180971901926399
def reachable : Nat := 9006836441821531849363132072516846333567931828534310503341635878518144157879369439436011466945390070364862727243157295680002701300611247910252677104157696
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
theorem oddSide_length : oddSide.length = 60 := by decide
theorem evenSide_length : evenSide.length = 58 := by decide

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

end Snake9.Regrowth.E112104
