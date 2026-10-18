import RegrowthParityCounts
namespace Snake9.Regrowth.E112199
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[145, 144, 146, 130, 131, 139, 137, 141, 140, 156, 158, 159, 151, 407, 405, 413, 409, 411, 410, 394, 398, 462, 478, 476, 472, 464, 466, 467, 451, 459, 457, 461, 453, 452, 388, 260, 261, 269, 265, 267, 259, 275, 274, 272, 280, 284, 286, 287, 351, 347, 345, 337, 341, 340, 342, 326, 322, 330, 328, 332, 76, 92, 88, 80, 82, 83, 87, 119, 55, 63, 62, 60, 56, 48, 50, 34, 35, 43, 41, 45, 37, 36, 100, 228, 229, 237, 233, 235, 227, 243, 242, 240, 248, 252, 254, 255, 511, 507, 505, 497, 501, 500, 502, 486, 482, 490, 488, 492, 428, 444, 440, 432]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (7 : Vertex), (8 : Vertex), (10 : Vertex), (14 : Vertex), (15 : Vertex), (20 : Vertex), (21 : Vertex), (22 : Vertex), (25 : Vertex), (26 : Vertex), (27 : Vertex), (29 : Vertex), (65 : Vertex), (69 : Vertex), (73 : Vertex), (75 : Vertex), (79 : Vertex), (97 : Vertex), (104 : Vertex), (106 : Vertex), (110 : Vertex), (111 : Vertex), (113 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (170 : Vertex), (174 : Vertex), (175 : Vertex), (180 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (202 : Vertex), (207 : Vertex), (212 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (298 : Vertex), (302 : Vertex), (303 : Vertex), (305 : Vertex), (308 : Vertex), (309 : Vertex), (310 : Vertex), (313 : Vertex), (314 : Vertex), (315 : Vertex), (317 : Vertex), (352 : Vertex), (353 : Vertex), (355 : Vertex), (357 : Vertex), (359 : Vertex), (361 : Vertex), (363 : Vertex), (365 : Vertex), (366 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (371 : Vertex), (376 : Vertex), (378 : Vertex), (380 : Vertex), (381 : Vertex), (382 : Vertex), (385 : Vertex), (416 : Vertex), (417 : Vertex), (419 : Vertex), (421 : Vertex), (423 : Vertex), (425 : Vertex), (427 : Vertex), (431 : Vertex), (432 : Vertex), (434 : Vertex), (435 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (8 : Vertex), (14 : Vertex), (21 : Vertex), (22 : Vertex), (25 : Vertex), (26 : Vertex), (69 : Vertex), (73 : Vertex), (79 : Vertex), (97 : Vertex), (104 : Vertex), (110 : Vertex), (121 : Vertex), (122 : Vertex), (161 : Vertex), (167 : Vertex), (168 : Vertex), (174 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (289 : Vertex), (295 : Vertex), (296 : Vertex), (302 : Vertex), (309 : Vertex), (310 : Vertex), (313 : Vertex), (314 : Vertex), (352 : Vertex), (355 : Vertex), (357 : Vertex), (361 : Vertex), (367 : Vertex), (370 : Vertex), (376 : Vertex), (381 : Vertex), (382 : Vertex), (385 : Vertex), (416 : Vertex), (419 : Vertex), (421 : Vertex), (425 : Vertex), (431 : Vertex), (434 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (10 : Vertex), (15 : Vertex), (20 : Vertex), (27 : Vertex), (29 : Vertex), (65 : Vertex), (75 : Vertex), (106 : Vertex), (111 : Vertex), (113 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (166 : Vertex), (170 : Vertex), (175 : Vertex), (180 : Vertex), (187 : Vertex), (189 : Vertex), (192 : Vertex), (198 : Vertex), (202 : Vertex), (207 : Vertex), (212 : Vertex), (219 : Vertex), (221 : Vertex), (288 : Vertex), (294 : Vertex), (298 : Vertex), (303 : Vertex), (305 : Vertex), (308 : Vertex), (315 : Vertex), (317 : Vertex), (353 : Vertex), (359 : Vertex), (363 : Vertex), (365 : Vertex), (366 : Vertex), (368 : Vertex), (371 : Vertex), (378 : Vertex), (380 : Vertex), (417 : Vertex), (423 : Vertex), (427 : Vertex), (432 : Vertex), (435 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (7 : Vertex), (8 : Vertex), (10 : Vertex), (14 : Vertex), (15 : Vertex), (20 : Vertex), (21 : Vertex), (22 : Vertex), (25 : Vertex), (26 : Vertex), (27 : Vertex), (29 : Vertex), (65 : Vertex), (69 : Vertex), (73 : Vertex), (75 : Vertex), (79 : Vertex), (97 : Vertex), (104 : Vertex), (106 : Vertex), (110 : Vertex), (111 : Vertex), (113 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (170 : Vertex), (174 : Vertex), (175 : Vertex), (180 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (202 : Vertex), (207 : Vertex), (212 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (298 : Vertex), (302 : Vertex), (303 : Vertex), (305 : Vertex), (308 : Vertex), (309 : Vertex), (310 : Vertex), (313 : Vertex), (314 : Vertex), (315 : Vertex), (317 : Vertex), (352 : Vertex), (353 : Vertex), (355 : Vertex), (357 : Vertex), (359 : Vertex), (361 : Vertex), (363 : Vertex), (365 : Vertex), (366 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (371 : Vertex), (376 : Vertex), (378 : Vertex), (380 : Vertex), (381 : Vertex), (382 : Vertex), (385 : Vertex), (416 : Vertex), (417 : Vertex), (419 : Vertex), (421 : Vertex), (423 : Vertex), (425 : Vertex), (427 : Vertex), (431 : Vertex), (434 : Vertex), (435 : Vertex)]
def head : Vertex := 432
def ban : Nat := 13407807929942597099573885902553114290500322095422257660255376727976594203365622577706842997914755411153372544843463451321524757622285577414340642480273980
def reachable : Nat := 139095652731836979043725170135717468184715745169826707924399095031300252148016536659313343022599532229125189660992532093006525810115
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
theorem oddSide_length : oddSide.length = 55 := by decide
theorem evenSide_length : evenSide.length = 50 := by decide

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

end Snake9.Regrowth.E112199
