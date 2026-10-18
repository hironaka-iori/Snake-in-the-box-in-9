import RegrowthParityCounts
namespace Snake9.Regrowth.E112051
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[199, 198, 214, 212, 213, 209, 217, 219, 218, 202, 200, 192, 448, 464, 466, 467, 451, 459, 457, 461, 477, 476, 478, 462, 398, 394, 410, 411, 409, 401, 405, 407, 151, 159, 158, 156, 152, 144, 146, 130, 131, 139, 137, 141, 133, 132, 388, 260, 261, 269, 265, 267, 259, 275, 274, 272, 280, 284, 286, 287, 351, 347, 345, 337, 341, 340, 342, 326, 322, 330, 328, 332, 76, 92, 88, 80, 82, 83, 87, 119, 55, 63, 62, 60, 56, 48, 50, 34, 35, 43, 41, 45, 37, 36, 100, 228, 229, 237, 233, 235, 227, 243, 242, 240, 248, 252, 254, 255, 511, 507, 505, 497]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (7 : Vertex), (8 : Vertex), (10 : Vertex), (14 : Vertex), (15 : Vertex), (17 : Vertex), (20 : Vertex), (21 : Vertex), (22 : Vertex), (25 : Vertex), (26 : Vertex), (27 : Vertex), (29 : Vertex), (65 : Vertex), (69 : Vertex), (73 : Vertex), (75 : Vertex), (79 : Vertex), (97 : Vertex), (104 : Vertex), (106 : Vertex), (110 : Vertex), (111 : Vertex), (113 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (170 : Vertex), (172 : Vertex), (174 : Vertex), (175 : Vertex), (177 : Vertex), (180 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (298 : Vertex), (300 : Vertex), (302 : Vertex), (303 : Vertex), (305 : Vertex), (308 : Vertex), (309 : Vertex), (310 : Vertex), (313 : Vertex), (314 : Vertex), (315 : Vertex), (317 : Vertex), (352 : Vertex), (353 : Vertex), (355 : Vertex), (357 : Vertex), (359 : Vertex), (361 : Vertex), (363 : Vertex), (365 : Vertex), (366 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (371 : Vertex), (376 : Vertex), (378 : Vertex), (380 : Vertex), (381 : Vertex), (382 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (419 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (431 : Vertex), (432 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (438 : Vertex), (440 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (481 : Vertex), (482 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (490 : Vertex), (492 : Vertex), (497 : Vertex), (500 : Vertex), (501 : Vertex), (502 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (8 : Vertex), (14 : Vertex), (21 : Vertex), (22 : Vertex), (25 : Vertex), (26 : Vertex), (69 : Vertex), (73 : Vertex), (79 : Vertex), (97 : Vertex), (104 : Vertex), (110 : Vertex), (121 : Vertex), (122 : Vertex), (161 : Vertex), (167 : Vertex), (168 : Vertex), (174 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (289 : Vertex), (295 : Vertex), (296 : Vertex), (302 : Vertex), (309 : Vertex), (310 : Vertex), (313 : Vertex), (314 : Vertex), (352 : Vertex), (355 : Vertex), (357 : Vertex), (361 : Vertex), (367 : Vertex), (370 : Vertex), (376 : Vertex), (381 : Vertex), (382 : Vertex), (416 : Vertex), (419 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (428 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (440 : Vertex), (445 : Vertex), (446 : Vertex), (481 : Vertex), (482 : Vertex), (487 : Vertex), (488 : Vertex), (501 : Vertex), (502 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (10 : Vertex), (15 : Vertex), (17 : Vertex), (20 : Vertex), (27 : Vertex), (29 : Vertex), (65 : Vertex), (75 : Vertex), (106 : Vertex), (111 : Vertex), (113 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (166 : Vertex), (170 : Vertex), (172 : Vertex), (175 : Vertex), (177 : Vertex), (180 : Vertex), (187 : Vertex), (189 : Vertex), (288 : Vertex), (294 : Vertex), (298 : Vertex), (300 : Vertex), (303 : Vertex), (305 : Vertex), (308 : Vertex), (315 : Vertex), (317 : Vertex), (353 : Vertex), (359 : Vertex), (363 : Vertex), (365 : Vertex), (366 : Vertex), (368 : Vertex), (371 : Vertex), (378 : Vertex), (380 : Vertex), (417 : Vertex), (418 : Vertex), (423 : Vertex), (424 : Vertex), (427 : Vertex), (429 : Vertex), (432 : Vertex), (435 : Vertex), (438 : Vertex), (444 : Vertex), (486 : Vertex), (490 : Vertex), (492 : Vertex), (497 : Vertex), (500 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (7 : Vertex), (8 : Vertex), (10 : Vertex), (14 : Vertex), (15 : Vertex), (17 : Vertex), (20 : Vertex), (21 : Vertex), (22 : Vertex), (25 : Vertex), (26 : Vertex), (27 : Vertex), (29 : Vertex), (65 : Vertex), (69 : Vertex), (73 : Vertex), (75 : Vertex), (79 : Vertex), (97 : Vertex), (104 : Vertex), (106 : Vertex), (110 : Vertex), (111 : Vertex), (113 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (170 : Vertex), (172 : Vertex), (174 : Vertex), (175 : Vertex), (177 : Vertex), (180 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (298 : Vertex), (300 : Vertex), (302 : Vertex), (303 : Vertex), (305 : Vertex), (308 : Vertex), (309 : Vertex), (310 : Vertex), (313 : Vertex), (314 : Vertex), (315 : Vertex), (317 : Vertex), (352 : Vertex), (353 : Vertex), (355 : Vertex), (357 : Vertex), (359 : Vertex), (361 : Vertex), (363 : Vertex), (365 : Vertex), (366 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (371 : Vertex), (376 : Vertex), (378 : Vertex), (380 : Vertex), (381 : Vertex), (382 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (419 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (431 : Vertex), (432 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (438 : Vertex), (440 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (481 : Vertex), (482 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (490 : Vertex), (492 : Vertex), (500 : Vertex), (501 : Vertex), (502 : Vertex)]
def head : Vertex := 497
def ban : Nat := 13384876795060904644821364218692462490409056027257169673209467760288966758476136467899790317984436807738855265414012253806940513066696415994661162948835900
def reachable : Nat := 22931134881692454752660779513383637070309793335223704514093683432797271597410508902083980182466619951176592772473797046813369745250153951772486057248195
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
theorem evenSide_length : evenSide.length = 57 := by decide

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

end Snake9.Regrowth.E112051
