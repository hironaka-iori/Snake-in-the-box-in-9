import RegrowthParityCounts
namespace Snake9.Regrowth.E112022
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 16, 272, 280, 281, 283, 287, 279, 277, 261, 260, 268, 270, 266, 258, 259, 3, 131, 130, 138, 142, 140, 132, 148, 149, 151, 159, 155, 153, 152, 216, 220, 222, 214, 210, 211, 209, 193, 197, 205, 207, 203, 459, 475, 479, 471, 469, 468, 452, 454, 390, 391, 399, 397, 413, 412, 414, 410, 402, 403, 401, 385, 384, 392, 456, 328, 320, 321, 337, 339, 338, 342, 350, 348, 349, 333, 335, 327, 71, 87, 85, 84, 68, 76, 78, 74, 90, 91, 89, 73, 9, 13, 29, 28, 30, 22, 6, 38, 294, 295, 303, 301, 297, 289, 305, 307, 306, 314, 318, 316, 308, 52]
def region : List Vertex := [(37 : Vertex), (40 : Vertex), (42 : Vertex), (43 : Vertex), (44 : Vertex), (52 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (59 : Vertex), (63 : Vertex), (96 : Vertex), (97 : Vertex), (98 : Vertex), (99 : Vertex), (101 : Vertex), (104 : Vertex), (107 : Vertex), (109 : Vertex), (111 : Vertex), (112 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (118 : Vertex), (120 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (127 : Vertex), (160 : Vertex), (161 : Vertex), (165 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (171 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (224 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (238 : Vertex), (240 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (253 : Vertex), (255 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (362 : Vertex), (363 : Vertex), (364 : Vertex), (366 : Vertex), (368 : Vertex), (373 : Vertex), (375 : Vertex), (376 : Vertex), (377 : Vertex), (379 : Vertex), (383 : Vertex), (418 : Vertex), (419 : Vertex), (420 : Vertex), (421 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (430 : Vertex), (432 : Vertex), (437 : Vertex), (438 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (483 : Vertex), (485 : Vertex), (487 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex), (493 : Vertex), (494 : Vertex), (495 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (504 : Vertex), (505 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(37 : Vertex), (42 : Vertex), (44 : Vertex), (52 : Vertex), (55 : Vertex), (56 : Vertex), (59 : Vertex), (97 : Vertex), (98 : Vertex), (104 : Vertex), (107 : Vertex), (109 : Vertex), (112 : Vertex), (115 : Vertex), (118 : Vertex), (124 : Vertex), (127 : Vertex), (161 : Vertex), (167 : Vertex), (168 : Vertex), (171 : Vertex), (173 : Vertex), (176 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (224 : Vertex), (227 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (244 : Vertex), (247 : Vertex), (251 : Vertex), (253 : Vertex), (355 : Vertex), (357 : Vertex), (362 : Vertex), (364 : Vertex), (375 : Vertex), (376 : Vertex), (379 : Vertex), (419 : Vertex), (421 : Vertex), (426 : Vertex), (428 : Vertex), (439 : Vertex), (440 : Vertex), (443 : Vertex), (481 : Vertex), (482 : Vertex), (487 : Vertex), (493 : Vertex), (494 : Vertex), (496 : Vertex), (499 : Vertex), (502 : Vertex), (505 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(40 : Vertex), (43 : Vertex), (53 : Vertex), (57 : Vertex), (63 : Vertex), (96 : Vertex), (99 : Vertex), (101 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (120 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (165 : Vertex), (169 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (189 : Vertex), (190 : Vertex), (226 : Vertex), (228 : Vertex), (231 : Vertex), (232 : Vertex), (238 : Vertex), (240 : Vertex), (245 : Vertex), (249 : Vertex), (250 : Vertex), (255 : Vertex), (354 : Vertex), (356 : Vertex), (363 : Vertex), (366 : Vertex), (368 : Vertex), (373 : Vertex), (377 : Vertex), (383 : Vertex), (418 : Vertex), (420 : Vertex), (427 : Vertex), (430 : Vertex), (432 : Vertex), (437 : Vertex), (438 : Vertex), (441 : Vertex), (447 : Vertex), (480 : Vertex), (483 : Vertex), (485 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (504 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(37 : Vertex), (40 : Vertex), (42 : Vertex), (43 : Vertex), (44 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (59 : Vertex), (63 : Vertex), (96 : Vertex), (97 : Vertex), (98 : Vertex), (99 : Vertex), (101 : Vertex), (104 : Vertex), (107 : Vertex), (109 : Vertex), (111 : Vertex), (112 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (118 : Vertex), (120 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (127 : Vertex), (160 : Vertex), (161 : Vertex), (165 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (171 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (224 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex), (238 : Vertex), (240 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (253 : Vertex), (255 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (362 : Vertex), (363 : Vertex), (364 : Vertex), (366 : Vertex), (368 : Vertex), (373 : Vertex), (375 : Vertex), (376 : Vertex), (377 : Vertex), (379 : Vertex), (383 : Vertex), (418 : Vertex), (419 : Vertex), (420 : Vertex), (421 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (430 : Vertex), (432 : Vertex), (437 : Vertex), (438 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (483 : Vertex), (485 : Vertex), (487 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex), (493 : Vertex), (494 : Vertex), (495 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (504 : Vertex), (505 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 52
def ban : Nat := 7158912704839154772963167599897758386061791434951627921919157702039007031605081581743286679986038998500587915347959376641525339281046730637955451867627519
def reachable : Nat := 6248895225103442326610857398308087741417574385640765455804403741682756998468465395058587618180864429189443942838526674212228543530899839308478197138456576
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
theorem oddSide_length : oddSide.length = 62 := by decide
theorem evenSide_length : evenSide.length = 61 := by decide

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

end Snake9.Regrowth.E112022
