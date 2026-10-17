import RegrowthParityCounts
namespace Snake9.Regrowth.E112246
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 17, 19, 18, 22, 30, 28, 29, 13, 15, 7, 263, 279, 277, 276, 260, 268, 270, 266, 282, 283, 281, 265, 329, 333, 349, 348, 350, 342, 326, 358, 102, 103, 111, 109, 125, 124, 126, 122, 114, 115, 113, 97, 96, 104, 360, 488, 480, 481, 497, 499, 498, 502, 510, 508, 509, 493, 495, 487, 423, 439, 437, 436, 420, 428, 430, 426, 442, 443, 441, 425, 169, 173, 189, 188, 190, 182, 166, 134, 198, 199, 207, 205, 221, 220, 222, 218, 210, 211, 209, 193, 192, 200, 136, 392, 384, 385, 401, 403, 402, 406, 414, 412, 413, 397, 399, 395, 139, 155, 159, 151]
def region : List Vertex := [(34 : Vertex), (35 : Vertex), (36 : Vertex), (37 : Vertex), (42 : Vertex), (43 : Vertex), (44 : Vertex), (46 : Vertex), (48 : Vertex), (52 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (59 : Vertex), (63 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (74 : Vertex), (75 : Vertex), (76 : Vertex), (78 : Vertex), (80 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (91 : Vertex), (95 : Vertex), (133 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (160 : Vertex), (163 : Vertex), (176 : Vertex), (177 : Vertex), (179 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (240 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (290 : Vertex), (291 : Vertex), (293 : Vertex), (299 : Vertex), (301 : Vertex), (303 : Vertex), (304 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (312 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (319 : Vertex), (320 : Vertex), (323 : Vertex), (336 : Vertex), (337 : Vertex), (339 : Vertex), (355 : Vertex), (357 : Vertex), (363 : Vertex), (368 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (377 : Vertex), (379 : Vertex), (383 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (458 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(35 : Vertex), (37 : Vertex), (42 : Vertex), (44 : Vertex), (52 : Vertex), (55 : Vertex), (56 : Vertex), (59 : Vertex), (67 : Vertex), (69 : Vertex), (74 : Vertex), (76 : Vertex), (84 : Vertex), (87 : Vertex), (88 : Vertex), (91 : Vertex), (133 : Vertex), (148 : Vertex), (151 : Vertex), (176 : Vertex), (179 : Vertex), (227 : Vertex), (229 : Vertex), (234 : Vertex), (236 : Vertex), (244 : Vertex), (247 : Vertex), (248 : Vertex), (251 : Vertex), (289 : Vertex), (290 : Vertex), (299 : Vertex), (301 : Vertex), (304 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (319 : Vertex), (336 : Vertex), (339 : Vertex), (355 : Vertex), (357 : Vertex), (372 : Vertex), (375 : Vertex), (379 : Vertex), (451 : Vertex), (453 : Vertex), (458 : Vertex), (460 : Vertex), (468 : Vertex), (471 : Vertex), (472 : Vertex), (475 : Vertex)]
def evenSide : List Vertex := [(34 : Vertex), (36 : Vertex), (43 : Vertex), (46 : Vertex), (48 : Vertex), (53 : Vertex), (57 : Vertex), (63 : Vertex), (66 : Vertex), (68 : Vertex), (75 : Vertex), (78 : Vertex), (80 : Vertex), (85 : Vertex), (89 : Vertex), (95 : Vertex), (144 : Vertex), (149 : Vertex), (160 : Vertex), (163 : Vertex), (177 : Vertex), (226 : Vertex), (228 : Vertex), (235 : Vertex), (238 : Vertex), (240 : Vertex), (245 : Vertex), (249 : Vertex), (255 : Vertex), (288 : Vertex), (291 : Vertex), (293 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (312 : Vertex), (317 : Vertex), (318 : Vertex), (320 : Vertex), (323 : Vertex), (337 : Vertex), (363 : Vertex), (368 : Vertex), (373 : Vertex), (377 : Vertex), (383 : Vertex), (450 : Vertex), (452 : Vertex), (462 : Vertex), (464 : Vertex), (469 : Vertex), (473 : Vertex), (479 : Vertex)]
def others : List Vertex := [(34 : Vertex), (35 : Vertex), (36 : Vertex), (37 : Vertex), (42 : Vertex), (43 : Vertex), (44 : Vertex), (46 : Vertex), (48 : Vertex), (52 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (59 : Vertex), (63 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (74 : Vertex), (75 : Vertex), (76 : Vertex), (78 : Vertex), (80 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (91 : Vertex), (95 : Vertex), (133 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (160 : Vertex), (163 : Vertex), (176 : Vertex), (177 : Vertex), (179 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (240 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (290 : Vertex), (291 : Vertex), (293 : Vertex), (299 : Vertex), (301 : Vertex), (303 : Vertex), (304 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (312 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (319 : Vertex), (320 : Vertex), (323 : Vertex), (336 : Vertex), (337 : Vertex), (339 : Vertex), (355 : Vertex), (357 : Vertex), (363 : Vertex), (368 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (377 : Vertex), (379 : Vertex), (383 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (458 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex)]
def head : Vertex := 151
def ban : Nat := 13407807928239138281677915550763191535117114232872202058031843684797195267844120109418796564735602058139153861628629975940795249770852783402643517884858367
def reachable : Nat := 1703458817896109447442654592362251587720191319691717758924568762229426867383077733431301369550877996557856074912958633041093786543790131121225728
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
theorem evenSide_length : evenSide.length = 53 := by decide

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

end Snake9.Regrowth.E112246
