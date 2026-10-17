import RegrowthParityCounts
namespace Snake9.Regrowth.E112069
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[280, 281, 265, 267, 266, 258, 262, 260, 261, 277, 279, 287, 286, 350, 348, 349, 333, 335, 327, 323, 339, 83, 87, 85, 69, 68, 70, 78, 74, 75, 73, 89, 88, 80, 336, 464, 472, 473, 457, 459, 458, 462, 454, 452, 453, 469, 471, 479, 223, 207, 205, 204, 220, 212, 214, 210, 194, 195, 193, 209, 145, 149, 133, 132, 134, 142, 158, 190, 446, 447, 439, 437, 421, 420, 422, 418, 426, 427, 425, 441, 440, 432, 176, 48, 56, 57, 41, 43, 42, 46, 38, 36, 37, 53, 55, 63, 127, 111, 109, 108, 124, 116, 118, 114, 98, 99, 97, 113, 369, 373, 357, 356]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (7 : Vertex), (8 : Vertex), (12 : Vertex), (13 : Vertex), (15 : Vertex), (18 : Vertex), (20 : Vertex), (22 : Vertex), (26 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (136 : Vertex), (137 : Vertex), (139 : Vertex), (152 : Vertex), (155 : Vertex), (161 : Vertex), (163 : Vertex), (167 : Vertex), (168 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (179 : Vertex), (187 : Vertex), (189 : Vertex), (224 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (238 : Vertex), (243 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (253 : Vertex), (288 : Vertex), (289 : Vertex), (291 : Vertex), (295 : Vertex), (296 : Vertex), (300 : Vertex), (301 : Vertex), (303 : Vertex), (306 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (314 : Vertex), (315 : Vertex), (316 : Vertex), (317 : Vertex), (328 : Vertex), (352 : Vertex), (356 : Vertex), (358 : Vertex), (360 : Vertex), (361 : Vertex), (362 : Vertex), (363 : Vertex), (366 : Vertex), (376 : Vertex), (378 : Vertex), (379 : Vertex), (384 : Vertex), (385 : Vertex), (387 : Vertex), (391 : Vertex), (392 : Vertex), (396 : Vertex), (397 : Vertex), (399 : Vertex), (402 : Vertex), (403 : Vertex), (404 : Vertex), (406 : Vertex), (410 : Vertex), (411 : Vertex), (412 : Vertex), (413 : Vertex), (480 : Vertex), (481 : Vertex), (483 : Vertex), (487 : Vertex), (488 : Vertex), (492 : Vertex), (493 : Vertex), (495 : Vertex), (498 : Vertex), (499 : Vertex), (500 : Vertex), (502 : Vertex), (506 : Vertex), (507 : Vertex), (508 : Vertex), (509 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (8 : Vertex), (13 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (137 : Vertex), (152 : Vertex), (155 : Vertex), (161 : Vertex), (167 : Vertex), (168 : Vertex), (173 : Vertex), (179 : Vertex), (224 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (247 : Vertex), (248 : Vertex), (251 : Vertex), (253 : Vertex), (289 : Vertex), (295 : Vertex), (296 : Vertex), (301 : Vertex), (307 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (328 : Vertex), (352 : Vertex), (358 : Vertex), (361 : Vertex), (362 : Vertex), (376 : Vertex), (379 : Vertex), (385 : Vertex), (391 : Vertex), (392 : Vertex), (397 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (481 : Vertex), (487 : Vertex), (488 : Vertex), (493 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (12 : Vertex), (15 : Vertex), (18 : Vertex), (20 : Vertex), (27 : Vertex), (29 : Vertex), (136 : Vertex), (139 : Vertex), (163 : Vertex), (172 : Vertex), (175 : Vertex), (187 : Vertex), (189 : Vertex), (228 : Vertex), (231 : Vertex), (232 : Vertex), (235 : Vertex), (238 : Vertex), (243 : Vertex), (245 : Vertex), (249 : Vertex), (250 : Vertex), (288 : Vertex), (291 : Vertex), (300 : Vertex), (303 : Vertex), (306 : Vertex), (308 : Vertex), (315 : Vertex), (317 : Vertex), (356 : Vertex), (360 : Vertex), (363 : Vertex), (366 : Vertex), (378 : Vertex), (384 : Vertex), (387 : Vertex), (396 : Vertex), (399 : Vertex), (402 : Vertex), (404 : Vertex), (411 : Vertex), (413 : Vertex), (480 : Vertex), (483 : Vertex), (492 : Vertex), (495 : Vertex), (498 : Vertex), (500 : Vertex), (507 : Vertex), (509 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (7 : Vertex), (8 : Vertex), (12 : Vertex), (13 : Vertex), (15 : Vertex), (18 : Vertex), (20 : Vertex), (22 : Vertex), (26 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (136 : Vertex), (137 : Vertex), (139 : Vertex), (152 : Vertex), (155 : Vertex), (161 : Vertex), (163 : Vertex), (167 : Vertex), (168 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (179 : Vertex), (187 : Vertex), (189 : Vertex), (224 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (238 : Vertex), (243 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (253 : Vertex), (288 : Vertex), (289 : Vertex), (291 : Vertex), (295 : Vertex), (296 : Vertex), (300 : Vertex), (301 : Vertex), (303 : Vertex), (306 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (314 : Vertex), (315 : Vertex), (316 : Vertex), (317 : Vertex), (328 : Vertex), (352 : Vertex), (358 : Vertex), (360 : Vertex), (361 : Vertex), (362 : Vertex), (363 : Vertex), (366 : Vertex), (376 : Vertex), (378 : Vertex), (379 : Vertex), (384 : Vertex), (385 : Vertex), (387 : Vertex), (391 : Vertex), (392 : Vertex), (396 : Vertex), (397 : Vertex), (399 : Vertex), (402 : Vertex), (403 : Vertex), (404 : Vertex), (406 : Vertex), (410 : Vertex), (411 : Vertex), (412 : Vertex), (413 : Vertex), (480 : Vertex), (481 : Vertex), (483 : Vertex), (487 : Vertex), (488 : Vertex), (492 : Vertex), (493 : Vertex), (495 : Vertex), (498 : Vertex), (499 : Vertex), (500 : Vertex), (502 : Vertex), (506 : Vertex), (507 : Vertex), (508 : Vertex), (509 : Vertex)]
def head : Vertex := 356
def ban : Nat := 10246389063773537676445878523478998201045597571980949014350794508759458690991657605980977346697672739377856000383550602254500155954169013003569860214214260
def reachable : Nat := 3161418866169059423128146474726847926433768248611444363372766934962305339081889370820896951469230688312175857802935448599253726857777556942863788791869835
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

end Snake9.Regrowth.E112069
