import RegrowthParityCounts
namespace Snake9.Regrowth.E112261
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[295, 293, 261, 257, 321, 65, 69, 101, 229, 237, 233, 105, 107, 75, 79, 207, 199, 215, 87, 83, 115, 243, 251, 255, 127, 125, 93, 89, 217, 209, 208, 80, 84, 116, 118, 246, 230, 238, 110, 108, 76, 204, 220, 252, 248, 120, 122, 90, 218, 202, 194, 66, 70, 326, 342, 338, 466, 467, 451, 459, 457, 461, 333, 365, 367, 495, 487, 503, 375, 373, 341, 469, 468, 452, 484, 492, 488, 490, 362, 330, 328, 344, 348, 380, 382, 510, 478, 479, 351, 347, 379, 377, 505, 497, 496, 368, 352, 288, 290, 258, 386, 394, 410, 282, 314, 312, 440, 444, 412, 396, 268, 300]
def region : List Vertex := [(0 : Vertex), (3 : Vertex), (4 : Vertex), (7 : Vertex), (8 : Vertex), (9 : Vertex), (10 : Vertex), (13 : Vertex), (14 : Vertex), (17 : Vertex), (18 : Vertex), (21 : Vertex), (22 : Vertex), (24 : Vertex), (27 : Vertex), (28 : Vertex), (30 : Vertex), (31 : Vertex), (33 : Vertex), (35 : Vertex), (36 : Vertex), (38 : Vertex), (40 : Vertex), (42 : Vertex), (45 : Vertex), (47 : Vertex), (48 : Vertex), (49 : Vertex), (50 : Vertex), (53 : Vertex), (55 : Vertex), (57 : Vertex), (59 : Vertex), (60 : Vertex), (62 : Vertex), (128 : Vertex), (129 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex), (158 : Vertex), (159 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (163 : Vertex), (164 : Vertex), (167 : Vertex), (168 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (180 : Vertex), (181 : Vertex), (183 : Vertex), (185 : Vertex), (186 : Vertex), (189 : Vertex), (190 : Vertex), (224 : Vertex), (267 : Vertex), (271 : Vertex), (272 : Vertex), (275 : Vertex), (276 : Vertex), (279 : Vertex), (281 : Vertex), (285 : Vertex), (297 : Vertex), (299 : Vertex), (300 : Vertex), (302 : Vertex), (305 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (317 : Vertex), (319 : Vertex), (391 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (406 : Vertex), (407 : Vertex), (409 : Vertex), (417 : Vertex), (419 : Vertex), (422 : Vertex), (425 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (434 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (443 : Vertex), (447 : Vertex)]
def oddSide : List Vertex := [(4 : Vertex), (7 : Vertex), (8 : Vertex), (13 : Vertex), (14 : Vertex), (21 : Vertex), (22 : Vertex), (28 : Vertex), (31 : Vertex), (35 : Vertex), (38 : Vertex), (42 : Vertex), (47 : Vertex), (49 : Vertex), (50 : Vertex), (55 : Vertex), (59 : Vertex), (62 : Vertex), (128 : Vertex), (131 : Vertex), (133 : Vertex), (134 : Vertex), (137 : Vertex), (146 : Vertex), (148 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex), (158 : Vertex), (161 : Vertex), (162 : Vertex), (164 : Vertex), (167 : Vertex), (168 : Vertex), (171 : Vertex), (176 : Vertex), (181 : Vertex), (185 : Vertex), (186 : Vertex), (224 : Vertex), (271 : Vertex), (276 : Vertex), (279 : Vertex), (285 : Vertex), (299 : Vertex), (302 : Vertex), (307 : Vertex), (310 : Vertex), (319 : Vertex), (391 : Vertex), (400 : Vertex), (406 : Vertex), (409 : Vertex), (419 : Vertex), (422 : Vertex), (425 : Vertex), (434 : Vertex), (443 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (9 : Vertex), (10 : Vertex), (17 : Vertex), (18 : Vertex), (24 : Vertex), (27 : Vertex), (30 : Vertex), (33 : Vertex), (36 : Vertex), (40 : Vertex), (45 : Vertex), (48 : Vertex), (53 : Vertex), (57 : Vertex), (60 : Vertex), (129 : Vertex), (132 : Vertex), (136 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex), (147 : Vertex), (149 : Vertex), (150 : Vertex), (159 : Vertex), (160 : Vertex), (163 : Vertex), (170 : Vertex), (172 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (180 : Vertex), (183 : Vertex), (189 : Vertex), (190 : Vertex), (267 : Vertex), (272 : Vertex), (275 : Vertex), (281 : Vertex), (297 : Vertex), (300 : Vertex), (305 : Vertex), (308 : Vertex), (317 : Vertex), (399 : Vertex), (401 : Vertex), (407 : Vertex), (417 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (447 : Vertex)]
def others : List Vertex := [(0 : Vertex), (3 : Vertex), (4 : Vertex), (7 : Vertex), (8 : Vertex), (9 : Vertex), (10 : Vertex), (13 : Vertex), (14 : Vertex), (17 : Vertex), (18 : Vertex), (21 : Vertex), (22 : Vertex), (24 : Vertex), (27 : Vertex), (28 : Vertex), (30 : Vertex), (31 : Vertex), (33 : Vertex), (35 : Vertex), (36 : Vertex), (38 : Vertex), (40 : Vertex), (42 : Vertex), (45 : Vertex), (47 : Vertex), (48 : Vertex), (49 : Vertex), (50 : Vertex), (53 : Vertex), (55 : Vertex), (57 : Vertex), (59 : Vertex), (60 : Vertex), (62 : Vertex), (128 : Vertex), (129 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex), (158 : Vertex), (159 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (163 : Vertex), (164 : Vertex), (167 : Vertex), (168 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (180 : Vertex), (181 : Vertex), (183 : Vertex), (185 : Vertex), (186 : Vertex), (189 : Vertex), (190 : Vertex), (224 : Vertex), (267 : Vertex), (271 : Vertex), (272 : Vertex), (275 : Vertex), (276 : Vertex), (279 : Vertex), (281 : Vertex), (285 : Vertex), (297 : Vertex), (299 : Vertex), (302 : Vertex), (305 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (317 : Vertex), (319 : Vertex), (391 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (406 : Vertex), (407 : Vertex), (409 : Vertex), (417 : Vertex), (419 : Vertex), (422 : Vertex), (425 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (434 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (443 : Vertex), (447 : Vertex)]
def head : Vertex := 300
def ban : Nat := 13407807929942597099186689527856892667661415756391698216634177048190227353138268095634809532963528396247650961900079936582915131113622035682379202014320742
def reachable : Nat := 387335470348953459817950064127303205377702107159990408285612099061574685549990035482778053426024582236007237840083940564530425022015385
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
theorem oddSide_length : oddSide.length = 58 := by decide
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

end Snake9.Regrowth.E112261
