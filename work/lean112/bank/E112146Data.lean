import RegrowthParityCounts
namespace Snake9.Regrowth.E112146
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 4, 6, 22, 23, 19, 275, 274, 272, 276, 284, 286, 270, 271, 263, 261, 257, 265, 264, 392, 456, 457, 449, 453, 455, 463, 462, 478, 476, 468, 464, 466, 467, 475, 411, 443, 447, 446, 444, 436, 432, 416, 160, 164, 166, 174, 170, 186, 184, 185, 189, 181, 183, 179, 243, 242, 240, 244, 252, 254, 255, 239, 231, 229, 225, 233, 232, 104, 360, 361, 353, 357, 359, 367, 366, 382, 380, 372, 368, 370, 371, 379, 123, 121, 125, 117, 119, 118, 102, 98, 34, 50, 48, 49, 33, 37, 39, 47, 63, 62, 60, 44, 300, 292, 294, 310, 311, 309, 317, 313, 312, 314]
def region : List Vertex := [(10 : Vertex), (11 : Vertex), (13 : Vertex), (24 : Vertex), (25 : Vertex), (26 : Vertex), (29 : Vertex), (65 : Vertex), (67 : Vertex), (69 : Vertex), (71 : Vertex), (73 : Vertex), (74 : Vertex), (75 : Vertex), (76 : Vertex), (77 : Vertex), (78 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (82 : Vertex), (84 : Vertex), (88 : Vertex), (90 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (129 : Vertex), (130 : Vertex), (131 : Vertex), (133 : Vertex), (135 : Vertex), (137 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (192 : Vertex), (194 : Vertex), (195 : Vertex), (196 : Vertex), (198 : Vertex), (202 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (209 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (216 : Vertex), (217 : Vertex), (218 : Vertex), (221 : Vertex), (291 : Vertex), (298 : Vertex), (299 : Vertex), (314 : Vertex), (320 : Vertex), (322 : Vertex), (323 : Vertex), (324 : Vertex), (326 : Vertex), (330 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (337 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (346 : Vertex), (349 : Vertex), (351 : Vertex), (386 : Vertex), (387 : Vertex), (388 : Vertex), (390 : Vertex), (397 : Vertex), (401 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (413 : Vertex), (419 : Vertex), (421 : Vertex), (423 : Vertex), (425 : Vertex), (429 : Vertex), (482 : Vertex), (483 : Vertex), (484 : Vertex), (486 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (497 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (506 : Vertex), (509 : Vertex)]
def oddSide : List Vertex := [(11 : Vertex), (13 : Vertex), (25 : Vertex), (26 : Vertex), (67 : Vertex), (69 : Vertex), (73 : Vertex), (74 : Vertex), (76 : Vertex), (79 : Vertex), (81 : Vertex), (82 : Vertex), (84 : Vertex), (88 : Vertex), (94 : Vertex), (131 : Vertex), (133 : Vertex), (137 : Vertex), (140 : Vertex), (143 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (158 : Vertex), (194 : Vertex), (196 : Vertex), (203 : Vertex), (205 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (299 : Vertex), (314 : Vertex), (322 : Vertex), (324 : Vertex), (331 : Vertex), (333 : Vertex), (341 : Vertex), (342 : Vertex), (345 : Vertex), (346 : Vertex), (351 : Vertex), (386 : Vertex), (388 : Vertex), (397 : Vertex), (405 : Vertex), (406 : Vertex), (419 : Vertex), (421 : Vertex), (425 : Vertex), (482 : Vertex), (484 : Vertex), (491 : Vertex), (493 : Vertex), (501 : Vertex), (502 : Vertex), (505 : Vertex), (506 : Vertex)]
def evenSide : List Vertex := [(10 : Vertex), (24 : Vertex), (29 : Vertex), (65 : Vertex), (71 : Vertex), (75 : Vertex), (77 : Vertex), (78 : Vertex), (80 : Vertex), (90 : Vertex), (92 : Vertex), (95 : Vertex), (129 : Vertex), (130 : Vertex), (135 : Vertex), (139 : Vertex), (141 : Vertex), (144 : Vertex), (156 : Vertex), (159 : Vertex), (192 : Vertex), (195 : Vertex), (198 : Vertex), (202 : Vertex), (204 : Vertex), (209 : Vertex), (215 : Vertex), (216 : Vertex), (221 : Vertex), (291 : Vertex), (298 : Vertex), (320 : Vertex), (323 : Vertex), (326 : Vertex), (330 : Vertex), (332 : Vertex), (337 : Vertex), (343 : Vertex), (344 : Vertex), (349 : Vertex), (387 : Vertex), (390 : Vertex), (401 : Vertex), (407 : Vertex), (413 : Vertex), (423 : Vertex), (429 : Vertex), (483 : Vertex), (486 : Vertex), (490 : Vertex), (492 : Vertex), (497 : Vertex), (503 : Vertex), (504 : Vertex), (509 : Vertex)]
def others : List Vertex := [(10 : Vertex), (11 : Vertex), (13 : Vertex), (24 : Vertex), (25 : Vertex), (26 : Vertex), (29 : Vertex), (65 : Vertex), (67 : Vertex), (69 : Vertex), (71 : Vertex), (73 : Vertex), (74 : Vertex), (75 : Vertex), (76 : Vertex), (77 : Vertex), (78 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (82 : Vertex), (84 : Vertex), (88 : Vertex), (90 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (129 : Vertex), (130 : Vertex), (131 : Vertex), (133 : Vertex), (135 : Vertex), (137 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (192 : Vertex), (194 : Vertex), (195 : Vertex), (196 : Vertex), (198 : Vertex), (202 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (209 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (216 : Vertex), (217 : Vertex), (218 : Vertex), (221 : Vertex), (291 : Vertex), (298 : Vertex), (299 : Vertex), (320 : Vertex), (322 : Vertex), (323 : Vertex), (324 : Vertex), (326 : Vertex), (330 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (337 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (346 : Vertex), (349 : Vertex), (351 : Vertex), (386 : Vertex), (387 : Vertex), (388 : Vertex), (390 : Vertex), (397 : Vertex), (401 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (413 : Vertex), (419 : Vertex), (421 : Vertex), (423 : Vertex), (425 : Vertex), (429 : Vertex), (482 : Vertex), (483 : Vertex), (484 : Vertex), (486 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (497 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (506 : Vertex), (509 : Vertex)]
def head : Vertex := 314
def ban : Nat := 11318927311020272086059897513044131841171503865420547716451199166714386715985441829407164338598852316682548807663477429943407043253145599953307278493340671
def reachable : Nat := 2088880618922325013514127485161714286307861955171845661272362277007377314088105147394709959568051111007483050523008620910346839558800969993126370512743424
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
theorem oddSide_length : oddSide.length = 59 := by decide
theorem evenSide_length : evenSide.length = 55 := by decide

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

end Snake9.Regrowth.E112146
