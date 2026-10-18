import RegrowthParityCounts
namespace Snake9.Regrowth.E112196
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 17, 19, 18, 26, 30, 28, 29, 13, 15, 7, 6, 70, 68, 69, 85, 87, 95, 91, 75, 331, 335, 333, 349, 348, 350, 342, 338, 339, 337, 321, 320, 328, 72, 200, 192, 193, 209, 211, 210, 214, 222, 220, 221, 205, 207, 199, 455, 471, 469, 468, 452, 460, 462, 458, 474, 475, 473, 457, 393, 397, 413, 412, 414, 406, 390, 422, 166, 167, 175, 173, 189, 188, 190, 186, 178, 179, 177, 161, 160, 168, 424, 296, 288, 289, 305, 307, 306, 310, 318, 316, 317, 301, 303, 295, 359, 375, 373, 372, 356, 364, 366, 362, 378, 379, 377, 361, 105, 109, 125, 124]
def region : List Vertex := [(34 : Vertex), (35 : Vertex), (36 : Vertex), (37 : Vertex), (42 : Vertex), (43 : Vertex), (44 : Vertex), (46 : Vertex), (48 : Vertex), (52 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (59 : Vertex), (63 : Vertex), (80 : Vertex), (96 : Vertex), (98 : Vertex), (99 : Vertex), (112 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (118 : Vertex), (120 : Vertex), (124 : Vertex), (126 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (159 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (240 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (255 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (266 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (384 : Vertex), (387 : Vertex), (400 : Vertex), (401 : Vertex), (403 : Vertex), (419 : Vertex), (421 : Vertex), (427 : Vertex), (432 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (441 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (483 : Vertex), (485 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (504 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(35 : Vertex), (37 : Vertex), (42 : Vertex), (44 : Vertex), (52 : Vertex), (55 : Vertex), (56 : Vertex), (59 : Vertex), (98 : Vertex), (112 : Vertex), (115 : Vertex), (118 : Vertex), (124 : Vertex), (131 : Vertex), (133 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (155 : Vertex), (227 : Vertex), (229 : Vertex), (234 : Vertex), (236 : Vertex), (244 : Vertex), (247 : Vertex), (248 : Vertex), (251 : Vertex), (259 : Vertex), (261 : Vertex), (266 : Vertex), (268 : Vertex), (276 : Vertex), (279 : Vertex), (280 : Vertex), (283 : Vertex), (400 : Vertex), (403 : Vertex), (419 : Vertex), (421 : Vertex), (436 : Vertex), (439 : Vertex), (443 : Vertex), (481 : Vertex), (482 : Vertex), (491 : Vertex), (493 : Vertex), (496 : Vertex), (499 : Vertex), (502 : Vertex), (508 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(34 : Vertex), (36 : Vertex), (43 : Vertex), (46 : Vertex), (48 : Vertex), (53 : Vertex), (57 : Vertex), (63 : Vertex), (80 : Vertex), (96 : Vertex), (99 : Vertex), (113 : Vertex), (114 : Vertex), (120 : Vertex), (126 : Vertex), (130 : Vertex), (132 : Vertex), (139 : Vertex), (142 : Vertex), (144 : Vertex), (149 : Vertex), (153 : Vertex), (159 : Vertex), (226 : Vertex), (228 : Vertex), (235 : Vertex), (238 : Vertex), (240 : Vertex), (245 : Vertex), (249 : Vertex), (255 : Vertex), (258 : Vertex), (260 : Vertex), (270 : Vertex), (272 : Vertex), (277 : Vertex), (281 : Vertex), (287 : Vertex), (384 : Vertex), (387 : Vertex), (401 : Vertex), (427 : Vertex), (432 : Vertex), (437 : Vertex), (441 : Vertex), (447 : Vertex), (480 : Vertex), (483 : Vertex), (485 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (504 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(34 : Vertex), (35 : Vertex), (36 : Vertex), (37 : Vertex), (42 : Vertex), (43 : Vertex), (44 : Vertex), (46 : Vertex), (48 : Vertex), (52 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (59 : Vertex), (63 : Vertex), (80 : Vertex), (96 : Vertex), (98 : Vertex), (99 : Vertex), (112 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (118 : Vertex), (120 : Vertex), (126 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (159 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (240 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (255 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (266 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (384 : Vertex), (387 : Vertex), (400 : Vertex), (401 : Vertex), (403 : Vertex), (419 : Vertex), (421 : Vertex), (427 : Vertex), (432 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (441 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (483 : Vertex), (485 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (504 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex), (511 : Vertex)]
def head : Vertex := 124
def ban : Nat := 769316972884752992880678365129817363968023920291542429020531371335647406944260121877707996226586790896649296767069489680729626483586914565695925456470015
def reachable : Nat := 12638490957057844106693346633076028763511341900300850948703030072386116623129286854924166301940316636793382561419416561173024256328359655380737723549614080
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

end Snake9.Regrowth.E112196
