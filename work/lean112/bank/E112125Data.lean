import RegrowthParityCounts
namespace Snake9.Regrowth.E112125
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[327, 335, 333, 349, 348, 350, 346, 338, 339, 337, 321, 320, 328, 72, 200, 192, 193, 209, 211, 210, 214, 222, 220, 221, 205, 207, 199, 135, 151, 149, 148, 132, 140, 142, 138, 154, 155, 153, 137, 393, 397, 413, 412, 414, 406, 402, 400, 464, 472, 473, 475, 479, 471, 469, 453, 452, 460, 462, 458, 450, 451, 387, 259, 258, 266, 270, 268, 260, 261, 277, 279, 287, 283, 281, 280, 24, 28, 29, 13, 15, 11, 75, 91, 95, 87, 85, 84, 80, 112, 368, 376, 377, 379, 383, 375, 373, 357, 356, 364, 366, 362, 354, 355, 99, 227, 226, 234, 238, 236, 228, 244, 245]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (32 : Vertex), (33 : Vertex), (34 : Vertex), (36 : Vertex), (37 : Vertex), (38 : Vertex), (39 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (44 : Vertex), (46 : Vertex), (49 : Vertex), (50 : Vertex), (51 : Vertex), (52 : Vertex), (53 : Vertex), (54 : Vertex), (55 : Vertex), (57 : Vertex), (58 : Vertex), (59 : Vertex), (62 : Vertex), (63 : Vertex), (66 : Vertex), (70 : Vertex), (78 : Vertex), (102 : Vertex), (105 : Vertex), (109 : Vertex), (111 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (161 : Vertex), (165 : Vertex), (166 : Vertex), (168 : Vertex), (171 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (184 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (191 : Vertex), (233 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (299 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (430 : Vertex), (431 : Vertex), (433 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (19 : Vertex), (22 : Vertex), (32 : Vertex), (37 : Vertex), (38 : Vertex), (41 : Vertex), (42 : Vertex), (44 : Vertex), (49 : Vertex), (50 : Vertex), (52 : Vertex), (55 : Vertex), (59 : Vertex), (62 : Vertex), (70 : Vertex), (109 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (161 : Vertex), (168 : Vertex), (171 : Vertex), (173 : Vertex), (176 : Vertex), (179 : Vertex), (182 : Vertex), (188 : Vertex), (191 : Vertex), (233 : Vertex), (247 : Vertex), (248 : Vertex), (251 : Vertex), (289 : Vertex), (295 : Vertex), (296 : Vertex), (299 : Vertex), (301 : Vertex), (307 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (416 : Vertex), (421 : Vertex), (422 : Vertex), (426 : Vertex), (428 : Vertex), (431 : Vertex), (433 : Vertex), (436 : Vertex), (439 : Vertex), (440 : Vertex), (443 : Vertex), (481 : Vertex), (487 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (17 : Vertex), (18 : Vertex), (33 : Vertex), (34 : Vertex), (36 : Vertex), (39 : Vertex), (40 : Vertex), (46 : Vertex), (51 : Vertex), (53 : Vertex), (54 : Vertex), (57 : Vertex), (58 : Vertex), (63 : Vertex), (66 : Vertex), (78 : Vertex), (102 : Vertex), (105 : Vertex), (111 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (165 : Vertex), (166 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (184 : Vertex), (189 : Vertex), (190 : Vertex), (245 : Vertex), (249 : Vertex), (255 : Vertex), (288 : Vertex), (294 : Vertex), (297 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (308 : Vertex), (317 : Vertex), (318 : Vertex), (417 : Vertex), (418 : Vertex), (420 : Vertex), (423 : Vertex), (424 : Vertex), (427 : Vertex), (430 : Vertex), (435 : Vertex), (437 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex), (480 : Vertex), (486 : Vertex), (489 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (32 : Vertex), (33 : Vertex), (34 : Vertex), (36 : Vertex), (37 : Vertex), (38 : Vertex), (39 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (44 : Vertex), (46 : Vertex), (49 : Vertex), (50 : Vertex), (51 : Vertex), (52 : Vertex), (53 : Vertex), (54 : Vertex), (55 : Vertex), (57 : Vertex), (58 : Vertex), (59 : Vertex), (62 : Vertex), (63 : Vertex), (66 : Vertex), (70 : Vertex), (78 : Vertex), (102 : Vertex), (105 : Vertex), (109 : Vertex), (111 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (161 : Vertex), (165 : Vertex), (166 : Vertex), (168 : Vertex), (171 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (184 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (191 : Vertex), (233 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (299 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (430 : Vertex), (431 : Vertex), (433 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 245
def ban : Nat := 7316299916068358152310744489833142742525467904948643202395343354047667266263988342620217679251939604814054090000241143649906132069500423456182375357218748
def reachable : Nat := 6091508013874238947263280508372703384953897915643750175328218089674096763809558634181656618914963822875977768186244907203847750742446146490251273648865347
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
theorem evenSide_length : evenSide.length = 64 := by decide

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

end Snake9.Regrowth.E112125
