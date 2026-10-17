import RegrowthParityCounts
namespace Snake9.Regrowth.E112048
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 8, 12, 14, 6, 22, 18, 82, 338, 346, 347, 345, 349, 341, 343, 327, 326, 334, 332, 328, 320, 321, 65, 193, 192, 200, 204, 206, 198, 214, 215, 213, 221, 217, 219, 218, 154, 158, 156, 148, 144, 145, 147, 131, 135, 143, 141, 137, 393, 409, 413, 405, 407, 406, 390, 388, 452, 453, 461, 463, 479, 478, 476, 472, 464, 465, 467, 451, 450, 458, 394, 266, 258, 259, 275, 273, 272, 280, 284, 286, 287, 271, 269, 261, 5, 21, 29, 25, 27, 11, 75, 79, 95, 94, 92, 84, 68, 100, 356, 357, 365, 367, 363, 355, 371, 369, 368, 376, 380, 382, 374, 118]
def region : List Vertex := [(33 : Vertex), (34 : Vertex), (35 : Vertex), (39 : Vertex), (41 : Vertex), (42 : Vertex), (45 : Vertex), (47 : Vertex), (48 : Vertex), (49 : Vertex), (51 : Vertex), (52 : Vertex), (55 : Vertex), (56 : Vertex), (58 : Vertex), (60 : Vertex), (62 : Vertex), (63 : Vertex), (98 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (106 : Vertex), (110 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (164 : Vertex), (165 : Vertex), (166 : Vertex), (168 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (174 : Vertex), (178 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (187 : Vertex), (189 : Vertex), (191 : Vertex), (226 : Vertex), (227 : Vertex), (229 : Vertex), (231 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (239 : Vertex), (240 : Vertex), (241 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (248 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (300 : Vertex), (302 : Vertex), (306 : Vertex), (308 : Vertex), (309 : Vertex), (311 : Vertex), (313 : Vertex), (314 : Vertex), (315 : Vertex), (317 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (419 : Vertex), (421 : Vertex), (423 : Vertex), (424 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (430 : Vertex), (431 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (440 : Vertex), (442 : Vertex), (443 : Vertex), (444 : Vertex), (446 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (492 : Vertex), (494 : Vertex), (498 : Vertex), (500 : Vertex), (501 : Vertex), (503 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (509 : Vertex)]
def oddSide : List Vertex := [(35 : Vertex), (41 : Vertex), (42 : Vertex), (47 : Vertex), (49 : Vertex), (52 : Vertex), (55 : Vertex), (56 : Vertex), (62 : Vertex), (98 : Vertex), (103 : Vertex), (104 : Vertex), (110 : Vertex), (117 : Vertex), (118 : Vertex), (121 : Vertex), (122 : Vertex), (161 : Vertex), (162 : Vertex), (164 : Vertex), (168 : Vertex), (171 : Vertex), (174 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (191 : Vertex), (227 : Vertex), (229 : Vertex), (233 : Vertex), (234 : Vertex), (239 : Vertex), (241 : Vertex), (242 : Vertex), (244 : Vertex), (248 : Vertex), (254 : Vertex), (289 : Vertex), (295 : Vertex), (296 : Vertex), (302 : Vertex), (309 : Vertex), (313 : Vertex), (314 : Vertex), (416 : Vertex), (419 : Vertex), (421 : Vertex), (428 : Vertex), (431 : Vertex), (433 : Vertex), (434 : Vertex), (436 : Vertex), (440 : Vertex), (443 : Vertex), (446 : Vertex), (481 : Vertex), (487 : Vertex), (488 : Vertex), (494 : Vertex), (501 : Vertex), (505 : Vertex), (506 : Vertex)]
def evenSide : List Vertex := [(33 : Vertex), (34 : Vertex), (39 : Vertex), (45 : Vertex), (48 : Vertex), (51 : Vertex), (58 : Vertex), (60 : Vertex), (63 : Vertex), (105 : Vertex), (106 : Vertex), (119 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (165 : Vertex), (166 : Vertex), (170 : Vertex), (172 : Vertex), (178 : Vertex), (183 : Vertex), (184 : Vertex), (187 : Vertex), (189 : Vertex), (226 : Vertex), (231 : Vertex), (235 : Vertex), (237 : Vertex), (240 : Vertex), (243 : Vertex), (252 : Vertex), (255 : Vertex), (288 : Vertex), (294 : Vertex), (297 : Vertex), (300 : Vertex), (306 : Vertex), (308 : Vertex), (311 : Vertex), (315 : Vertex), (317 : Vertex), (417 : Vertex), (418 : Vertex), (423 : Vertex), (424 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (432 : Vertex), (435 : Vertex), (442 : Vertex), (444 : Vertex), (447 : Vertex), (480 : Vertex), (486 : Vertex), (489 : Vertex), (492 : Vertex), (498 : Vertex), (500 : Vertex), (503 : Vertex), (507 : Vertex), (509 : Vertex)]
def others : List Vertex := [(33 : Vertex), (34 : Vertex), (35 : Vertex), (39 : Vertex), (41 : Vertex), (42 : Vertex), (45 : Vertex), (47 : Vertex), (48 : Vertex), (49 : Vertex), (51 : Vertex), (52 : Vertex), (55 : Vertex), (56 : Vertex), (58 : Vertex), (60 : Vertex), (62 : Vertex), (63 : Vertex), (98 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (106 : Vertex), (110 : Vertex), (117 : Vertex), (119 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (164 : Vertex), (165 : Vertex), (166 : Vertex), (168 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (174 : Vertex), (178 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (187 : Vertex), (189 : Vertex), (191 : Vertex), (226 : Vertex), (227 : Vertex), (229 : Vertex), (231 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (239 : Vertex), (240 : Vertex), (241 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (248 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (300 : Vertex), (302 : Vertex), (306 : Vertex), (308 : Vertex), (309 : Vertex), (311 : Vertex), (313 : Vertex), (314 : Vertex), (315 : Vertex), (317 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (419 : Vertex), (421 : Vertex), (423 : Vertex), (424 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (430 : Vertex), (431 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (440 : Vertex), (442 : Vertex), (443 : Vertex), (444 : Vertex), (446 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (492 : Vertex), (494 : Vertex), (498 : Vertex), (500 : Vertex), (501 : Vertex), (503 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (509 : Vertex)]
def head : Vertex := 118
def ban : Nat := 10961699858538040660757430611128300248497314437296098910450512567707290187359587290664941258024013986935281850259341556566651309011121692390084205294387199
def reachable : Nat := 2446108071404556438816594387077545878982051383296294467273048876014473842713959686136933040142889440754750007927144494287102573800824877556349443711696896
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
theorem evenSide_length : evenSide.length = 62 := by decide

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

end Snake9.Regrowth.E112048
