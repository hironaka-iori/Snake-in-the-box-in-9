import RegrowthParityCounts
namespace Snake9.Regrowth.E112259
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[103, 101, 69, 65, 321, 257, 261, 293, 421, 429, 425, 297, 299, 267, 271, 399, 391, 407, 279, 275, 307, 435, 443, 447, 319, 317, 285, 281, 409, 401, 400, 272, 276, 308, 310, 438, 422, 430, 302, 300, 268, 396, 412, 444, 440, 312, 314, 282, 410, 394, 386, 258, 290, 288, 352, 368, 496, 497, 505, 377, 379, 347, 351, 479, 478, 510, 382, 380, 348, 344, 328, 330, 362, 490, 488, 492, 484, 452, 468, 469, 341, 373, 375, 503, 487, 495, 367, 365, 333, 461, 457, 459, 451, 467, 466, 338, 342, 326, 70, 66, 194, 202, 218, 90, 122, 120, 248, 252, 220, 204, 76, 108]
def region : List Vertex := [(0 : Vertex), (3 : Vertex), (4 : Vertex), (7 : Vertex), (8 : Vertex), (9 : Vertex), (10 : Vertex), (13 : Vertex), (14 : Vertex), (17 : Vertex), (18 : Vertex), (21 : Vertex), (22 : Vertex), (24 : Vertex), (27 : Vertex), (28 : Vertex), (30 : Vertex), (31 : Vertex), (33 : Vertex), (35 : Vertex), (36 : Vertex), (38 : Vertex), (40 : Vertex), (42 : Vertex), (45 : Vertex), (47 : Vertex), (48 : Vertex), (49 : Vertex), (50 : Vertex), (53 : Vertex), (55 : Vertex), (57 : Vertex), (59 : Vertex), (60 : Vertex), (62 : Vertex), (75 : Vertex), (79 : Vertex), (80 : Vertex), (83 : Vertex), (84 : Vertex), (87 : Vertex), (89 : Vertex), (93 : Vertex), (105 : Vertex), (107 : Vertex), (108 : Vertex), (110 : Vertex), (113 : Vertex), (115 : Vertex), (116 : Vertex), (118 : Vertex), (125 : Vertex), (127 : Vertex), (128 : Vertex), (129 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex), (158 : Vertex), (159 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (163 : Vertex), (164 : Vertex), (167 : Vertex), (168 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (180 : Vertex), (181 : Vertex), (183 : Vertex), (185 : Vertex), (186 : Vertex), (189 : Vertex), (190 : Vertex), (199 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (224 : Vertex), (225 : Vertex), (227 : Vertex), (230 : Vertex), (233 : Vertex), (235 : Vertex), (237 : Vertex), (238 : Vertex), (242 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (251 : Vertex), (255 : Vertex)]
def oddSide : List Vertex := [(4 : Vertex), (7 : Vertex), (8 : Vertex), (13 : Vertex), (14 : Vertex), (21 : Vertex), (22 : Vertex), (28 : Vertex), (31 : Vertex), (35 : Vertex), (38 : Vertex), (42 : Vertex), (47 : Vertex), (49 : Vertex), (50 : Vertex), (55 : Vertex), (59 : Vertex), (62 : Vertex), (79 : Vertex), (84 : Vertex), (87 : Vertex), (93 : Vertex), (107 : Vertex), (110 : Vertex), (115 : Vertex), (118 : Vertex), (127 : Vertex), (128 : Vertex), (131 : Vertex), (133 : Vertex), (134 : Vertex), (137 : Vertex), (146 : Vertex), (148 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex), (158 : Vertex), (161 : Vertex), (162 : Vertex), (164 : Vertex), (167 : Vertex), (168 : Vertex), (171 : Vertex), (176 : Vertex), (181 : Vertex), (185 : Vertex), (186 : Vertex), (199 : Vertex), (208 : Vertex), (214 : Vertex), (217 : Vertex), (224 : Vertex), (227 : Vertex), (230 : Vertex), (233 : Vertex), (242 : Vertex), (251 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (9 : Vertex), (10 : Vertex), (17 : Vertex), (18 : Vertex), (24 : Vertex), (27 : Vertex), (30 : Vertex), (33 : Vertex), (36 : Vertex), (40 : Vertex), (45 : Vertex), (48 : Vertex), (53 : Vertex), (57 : Vertex), (60 : Vertex), (75 : Vertex), (80 : Vertex), (83 : Vertex), (89 : Vertex), (105 : Vertex), (108 : Vertex), (113 : Vertex), (116 : Vertex), (125 : Vertex), (129 : Vertex), (132 : Vertex), (136 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex), (147 : Vertex), (149 : Vertex), (150 : Vertex), (159 : Vertex), (160 : Vertex), (163 : Vertex), (170 : Vertex), (172 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (180 : Vertex), (183 : Vertex), (189 : Vertex), (190 : Vertex), (207 : Vertex), (209 : Vertex), (215 : Vertex), (225 : Vertex), (235 : Vertex), (237 : Vertex), (238 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (255 : Vertex)]
def others : List Vertex := [(0 : Vertex), (3 : Vertex), (4 : Vertex), (7 : Vertex), (8 : Vertex), (9 : Vertex), (10 : Vertex), (13 : Vertex), (14 : Vertex), (17 : Vertex), (18 : Vertex), (21 : Vertex), (22 : Vertex), (24 : Vertex), (27 : Vertex), (28 : Vertex), (30 : Vertex), (31 : Vertex), (33 : Vertex), (35 : Vertex), (36 : Vertex), (38 : Vertex), (40 : Vertex), (42 : Vertex), (45 : Vertex), (47 : Vertex), (48 : Vertex), (49 : Vertex), (50 : Vertex), (53 : Vertex), (55 : Vertex), (57 : Vertex), (59 : Vertex), (60 : Vertex), (62 : Vertex), (75 : Vertex), (79 : Vertex), (80 : Vertex), (83 : Vertex), (84 : Vertex), (87 : Vertex), (89 : Vertex), (93 : Vertex), (105 : Vertex), (107 : Vertex), (110 : Vertex), (113 : Vertex), (115 : Vertex), (116 : Vertex), (118 : Vertex), (125 : Vertex), (127 : Vertex), (128 : Vertex), (129 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex), (158 : Vertex), (159 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (163 : Vertex), (164 : Vertex), (167 : Vertex), (168 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (180 : Vertex), (181 : Vertex), (183 : Vertex), (185 : Vertex), (186 : Vertex), (189 : Vertex), (190 : Vertex), (199 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (224 : Vertex), (225 : Vertex), (227 : Vertex), (230 : Vertex), (233 : Vertex), (235 : Vertex), (237 : Vertex), (238 : Vertex), (242 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (251 : Vertex), (255 : Vertex)]
def head : Vertex := 108
def ban : Nat := 13407807929942597099574024998205846127479365820519001422011879155350217761423818488595886498409931441365765893487356432641524089243020041954175056095058022
def reachable : Nat := 61706100497720103586990364663121838748086177398279710685934292734570941278105
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

end Snake9.Regrowth.E112259
