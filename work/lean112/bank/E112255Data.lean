import RegrowthParityCounts
namespace Snake9.Regrowth.E112255
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[127, 125, 93, 89, 345, 281, 285, 317, 445, 437, 433, 305, 307, 275, 279, 407, 415, 399, 271, 267, 299, 427, 419, 423, 295, 293, 261, 257, 385, 393, 392, 264, 268, 300, 302, 430, 446, 438, 310, 308, 276, 404, 388, 420, 416, 288, 290, 258, 386, 402, 410, 282, 314, 312, 376, 360, 488, 489, 481, 353, 355, 323, 327, 455, 454, 486, 358, 356, 324, 320, 336, 338, 370, 498, 496, 500, 508, 476, 460, 461, 333, 365, 367, 495, 511, 503, 375, 373, 341, 469, 465, 467, 475, 459, 458, 330, 334, 350, 94, 90, 218, 210, 194, 66, 98, 96, 224, 228, 196, 212, 84, 116]
def region : List Vertex := [(0 : Vertex), (3 : Vertex), (4 : Vertex), (6 : Vertex), (7 : Vertex), (9 : Vertex), (10 : Vertex), (13 : Vertex), (14 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (21 : Vertex), (22 : Vertex), (24 : Vertex), (27 : Vertex), (28 : Vertex), (31 : Vertex), (33 : Vertex), (35 : Vertex), (36 : Vertex), (38 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (45 : Vertex), (47 : Vertex), (48 : Vertex), (50 : Vertex), (53 : Vertex), (55 : Vertex), (57 : Vertex), (59 : Vertex), (60 : Vertex), (62 : Vertex), (65 : Vertex), (69 : Vertex), (72 : Vertex), (75 : Vertex), (76 : Vertex), (79 : Vertex), (83 : Vertex), (87 : Vertex), (101 : Vertex), (103 : Vertex), (105 : Vertex), (107 : Vertex), (108 : Vertex), (110 : Vertex), (113 : Vertex), (115 : Vertex), (116 : Vertex), (118 : Vertex), (128 : Vertex), (131 : Vertex), (133 : Vertex), (134 : Vertex), (135 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (142 : Vertex), (144 : Vertex), (145 : Vertex), (147 : Vertex), (149 : Vertex), (150 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (156 : Vertex), (157 : Vertex), (158 : Vertex), (161 : Vertex), (162 : Vertex), (165 : Vertex), (166 : Vertex), (168 : Vertex), (169 : Vertex), (170 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (188 : Vertex), (191 : Vertex), (193 : Vertex), (200 : Vertex), (201 : Vertex), (206 : Vertex), (207 : Vertex), (215 : Vertex), (223 : Vertex), (227 : Vertex), (231 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (238 : Vertex), (241 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (254 : Vertex)]
def oddSide : List Vertex := [(4 : Vertex), (7 : Vertex), (13 : Vertex), (14 : Vertex), (16 : Vertex), (21 : Vertex), (22 : Vertex), (28 : Vertex), (31 : Vertex), (35 : Vertex), (38 : Vertex), (41 : Vertex), (42 : Vertex), (47 : Vertex), (50 : Vertex), (55 : Vertex), (59 : Vertex), (62 : Vertex), (69 : Vertex), (76 : Vertex), (79 : Vertex), (87 : Vertex), (103 : Vertex), (107 : Vertex), (110 : Vertex), (115 : Vertex), (118 : Vertex), (128 : Vertex), (131 : Vertex), (133 : Vertex), (134 : Vertex), (138 : Vertex), (140 : Vertex), (145 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex), (158 : Vertex), (161 : Vertex), (162 : Vertex), (168 : Vertex), (173 : Vertex), (176 : Vertex), (179 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (191 : Vertex), (193 : Vertex), (200 : Vertex), (206 : Vertex), (223 : Vertex), (227 : Vertex), (234 : Vertex), (241 : Vertex), (248 : Vertex), (251 : Vertex), (254 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (6 : Vertex), (9 : Vertex), (10 : Vertex), (17 : Vertex), (18 : Vertex), (24 : Vertex), (27 : Vertex), (33 : Vertex), (36 : Vertex), (40 : Vertex), (45 : Vertex), (48 : Vertex), (53 : Vertex), (57 : Vertex), (60 : Vertex), (65 : Vertex), (72 : Vertex), (75 : Vertex), (83 : Vertex), (101 : Vertex), (105 : Vertex), (108 : Vertex), (113 : Vertex), (116 : Vertex), (135 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex), (144 : Vertex), (147 : Vertex), (149 : Vertex), (150 : Vertex), (153 : Vertex), (156 : Vertex), (165 : Vertex), (166 : Vertex), (169 : Vertex), (170 : Vertex), (172 : Vertex), (175 : Vertex), (178 : Vertex), (180 : Vertex), (183 : Vertex), (184 : Vertex), (187 : Vertex), (201 : Vertex), (207 : Vertex), (215 : Vertex), (231 : Vertex), (235 : Vertex), (237 : Vertex), (238 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (249 : Vertex)]
def others : List Vertex := [(0 : Vertex), (3 : Vertex), (4 : Vertex), (6 : Vertex), (7 : Vertex), (9 : Vertex), (10 : Vertex), (13 : Vertex), (14 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (21 : Vertex), (22 : Vertex), (24 : Vertex), (27 : Vertex), (28 : Vertex), (31 : Vertex), (33 : Vertex), (35 : Vertex), (36 : Vertex), (38 : Vertex), (40 : Vertex), (41 : Vertex), (42 : Vertex), (45 : Vertex), (47 : Vertex), (48 : Vertex), (50 : Vertex), (53 : Vertex), (55 : Vertex), (57 : Vertex), (59 : Vertex), (60 : Vertex), (62 : Vertex), (65 : Vertex), (69 : Vertex), (72 : Vertex), (75 : Vertex), (76 : Vertex), (79 : Vertex), (83 : Vertex), (87 : Vertex), (101 : Vertex), (103 : Vertex), (105 : Vertex), (107 : Vertex), (108 : Vertex), (110 : Vertex), (113 : Vertex), (115 : Vertex), (118 : Vertex), (128 : Vertex), (131 : Vertex), (133 : Vertex), (134 : Vertex), (135 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (142 : Vertex), (144 : Vertex), (145 : Vertex), (147 : Vertex), (149 : Vertex), (150 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (156 : Vertex), (157 : Vertex), (158 : Vertex), (161 : Vertex), (162 : Vertex), (165 : Vertex), (166 : Vertex), (168 : Vertex), (169 : Vertex), (170 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (188 : Vertex), (191 : Vertex), (193 : Vertex), (200 : Vertex), (201 : Vertex), (206 : Vertex), (207 : Vertex), (215 : Vertex), (223 : Vertex), (227 : Vertex), (231 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (238 : Vertex), (241 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (254 : Vertex)]
def head : Vertex := 116
def ban : Nat := 13407807929942597099574024998205846127478134507898756050248177723718634542142104123451170950327700936117220265816337412251856240482354019074141011788208422
def reachable : Nat := 34111498501302630829107403928913564789350770290946509127397258517430093178585
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

end Snake9.Regrowth.E112255
