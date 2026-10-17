import RegrowthParityCounts
namespace Snake9.Regrowth.E112257
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[319, 317, 285, 281, 345, 89, 93, 125, 253, 245, 241, 113, 115, 83, 87, 215, 223, 207, 79, 75, 107, 235, 227, 231, 103, 101, 69, 65, 193, 201, 200, 72, 76, 108, 110, 238, 254, 246, 118, 116, 84, 212, 196, 228, 224, 96, 98, 66, 194, 210, 218, 90, 94, 350, 334, 330, 458, 459, 475, 467, 465, 469, 341, 373, 375, 503, 511, 495, 367, 365, 333, 461, 460, 476, 508, 500, 496, 498, 370, 338, 336, 320, 324, 356, 358, 486, 454, 455, 327, 323, 355, 353, 481, 489, 488, 360, 376, 312, 314, 282, 410, 402, 386, 258, 290, 288, 416, 420, 388, 404, 276, 308]
def region : List Vertex := [(0 : Vertex), (3 : Vertex), (4 : Vertex), (6 : Vertex), (7 : Vertex), (9 : Vertex), (10 : Vertex), (13 : Vertex), (14 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (21 : Vertex), (22 : Vertex), (24 : Vertex), (27 : Vertex), (28 : Vertex), (31 : Vertex), (33 : Vertex), (35 : Vertex), (36 : Vertex), (38 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (45 : Vertex), (47 : Vertex), (48 : Vertex), (50 : Vertex), (53 : Vertex), (55 : Vertex), (57 : Vertex), (59 : Vertex), (60 : Vertex), (62 : Vertex), (128 : Vertex), (131 : Vertex), (133 : Vertex), (134 : Vertex), (135 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (142 : Vertex), (144 : Vertex), (145 : Vertex), (147 : Vertex), (149 : Vertex), (150 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (156 : Vertex), (157 : Vertex), (158 : Vertex), (161 : Vertex), (162 : Vertex), (165 : Vertex), (166 : Vertex), (168 : Vertex), (169 : Vertex), (170 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (188 : Vertex), (191 : Vertex), (248 : Vertex), (257 : Vertex), (261 : Vertex), (264 : Vertex), (267 : Vertex), (268 : Vertex), (271 : Vertex), (275 : Vertex), (279 : Vertex), (293 : Vertex), (295 : Vertex), (297 : Vertex), (299 : Vertex), (300 : Vertex), (302 : Vertex), (305 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (385 : Vertex), (392 : Vertex), (393 : Vertex), (398 : Vertex), (399 : Vertex), (407 : Vertex), (415 : Vertex), (419 : Vertex), (423 : Vertex), (426 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (433 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (441 : Vertex), (443 : Vertex), (446 : Vertex)]
def oddSide : List Vertex := [(4 : Vertex), (7 : Vertex), (13 : Vertex), (14 : Vertex), (16 : Vertex), (21 : Vertex), (22 : Vertex), (28 : Vertex), (31 : Vertex), (35 : Vertex), (38 : Vertex), (41 : Vertex), (42 : Vertex), (47 : Vertex), (50 : Vertex), (55 : Vertex), (59 : Vertex), (62 : Vertex), (128 : Vertex), (131 : Vertex), (133 : Vertex), (134 : Vertex), (138 : Vertex), (140 : Vertex), (145 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex), (158 : Vertex), (161 : Vertex), (162 : Vertex), (168 : Vertex), (173 : Vertex), (176 : Vertex), (179 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (191 : Vertex), (248 : Vertex), (261 : Vertex), (268 : Vertex), (271 : Vertex), (279 : Vertex), (295 : Vertex), (299 : Vertex), (302 : Vertex), (307 : Vertex), (310 : Vertex), (385 : Vertex), (392 : Vertex), (398 : Vertex), (415 : Vertex), (419 : Vertex), (426 : Vertex), (433 : Vertex), (443 : Vertex), (446 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (6 : Vertex), (9 : Vertex), (10 : Vertex), (17 : Vertex), (18 : Vertex), (24 : Vertex), (27 : Vertex), (33 : Vertex), (36 : Vertex), (40 : Vertex), (45 : Vertex), (48 : Vertex), (53 : Vertex), (57 : Vertex), (60 : Vertex), (135 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex), (144 : Vertex), (147 : Vertex), (149 : Vertex), (150 : Vertex), (153 : Vertex), (156 : Vertex), (165 : Vertex), (166 : Vertex), (169 : Vertex), (170 : Vertex), (172 : Vertex), (175 : Vertex), (178 : Vertex), (180 : Vertex), (183 : Vertex), (184 : Vertex), (187 : Vertex), (257 : Vertex), (264 : Vertex), (267 : Vertex), (275 : Vertex), (293 : Vertex), (297 : Vertex), (300 : Vertex), (305 : Vertex), (308 : Vertex), (393 : Vertex), (399 : Vertex), (407 : Vertex), (423 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (441 : Vertex)]
def others : List Vertex := [(0 : Vertex), (3 : Vertex), (4 : Vertex), (6 : Vertex), (7 : Vertex), (9 : Vertex), (10 : Vertex), (13 : Vertex), (14 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (21 : Vertex), (22 : Vertex), (24 : Vertex), (27 : Vertex), (28 : Vertex), (31 : Vertex), (33 : Vertex), (35 : Vertex), (36 : Vertex), (38 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (45 : Vertex), (47 : Vertex), (48 : Vertex), (50 : Vertex), (53 : Vertex), (55 : Vertex), (57 : Vertex), (59 : Vertex), (60 : Vertex), (62 : Vertex), (128 : Vertex), (131 : Vertex), (133 : Vertex), (134 : Vertex), (135 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (142 : Vertex), (144 : Vertex), (145 : Vertex), (147 : Vertex), (149 : Vertex), (150 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (156 : Vertex), (157 : Vertex), (158 : Vertex), (161 : Vertex), (162 : Vertex), (165 : Vertex), (166 : Vertex), (168 : Vertex), (169 : Vertex), (170 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (188 : Vertex), (191 : Vertex), (248 : Vertex), (257 : Vertex), (261 : Vertex), (264 : Vertex), (267 : Vertex), (268 : Vertex), (271 : Vertex), (275 : Vertex), (279 : Vertex), (293 : Vertex), (295 : Vertex), (297 : Vertex), (299 : Vertex), (300 : Vertex), (302 : Vertex), (305 : Vertex), (307 : Vertex), (310 : Vertex), (385 : Vertex), (392 : Vertex), (393 : Vertex), (398 : Vertex), (399 : Vertex), (407 : Vertex), (415 : Vertex), (419 : Vertex), (423 : Vertex), (426 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (433 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (441 : Vertex), (443 : Vertex), (446 : Vertex)]
def head : Vertex := 308
def ban : Nat := 13407807929942597099362742865533458937885388306012721613647161765545760700066900993896857202413761733766849978167055749137611950217584187367429105383938342
def reachable : Nat := 211282132672387189592746201886034436601015958172873842075237241052815050544768309754299201214071013884535236773897228965229336497448665
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

end Snake9.Regrowth.E112257
