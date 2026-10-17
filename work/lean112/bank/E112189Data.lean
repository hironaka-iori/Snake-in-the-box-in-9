import RegrowthParityCounts
namespace Snake9.Regrowth.E112189
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[152, 153, 155, 159, 151, 149, 133, 132, 140, 142, 138, 130, 131, 387, 259, 258, 266, 270, 268, 260, 261, 277, 279, 287, 283, 281, 280, 272, 400, 402, 406, 414, 412, 413, 397, 393, 457, 473, 475, 474, 458, 462, 460, 452, 468, 469, 471, 455, 199, 207, 205, 221, 220, 222, 214, 210, 211, 209, 193, 192, 200, 72, 328, 320, 321, 337, 339, 338, 342, 350, 348, 349, 333, 335, 331, 75, 91, 95, 87, 85, 84, 80, 112, 48, 56, 57, 59, 63, 55, 53, 37, 36, 44, 46, 42, 34, 35, 99, 227, 226, 234, 238, 236, 228, 244, 245, 247, 255, 251, 249, 248, 504]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (7 : Vertex), (9 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (70 : Vertex), (78 : Vertex), (102 : Vertex), (105 : Vertex), (109 : Vertex), (111 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (171 : Vertex), (173 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (299 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (354 : Vertex), (356 : Vertex), (357 : Vertex), (358 : Vertex), (359 : Vertex), (361 : Vertex), (362 : Vertex), (364 : Vertex), (366 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (376 : Vertex), (377 : Vertex), (378 : Vertex), (379 : Vertex), (383 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (430 : Vertex), (431 : Vertex), (433 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (485 : Vertex), (486 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (504 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (13 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (70 : Vertex), (109 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (161 : Vertex), (167 : Vertex), (168 : Vertex), (171 : Vertex), (173 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (289 : Vertex), (295 : Vertex), (296 : Vertex), (299 : Vertex), (301 : Vertex), (307 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (357 : Vertex), (358 : Vertex), (361 : Vertex), (362 : Vertex), (364 : Vertex), (372 : Vertex), (375 : Vertex), (376 : Vertex), (379 : Vertex), (416 : Vertex), (421 : Vertex), (422 : Vertex), (426 : Vertex), (428 : Vertex), (431 : Vertex), (433 : Vertex), (436 : Vertex), (439 : Vertex), (440 : Vertex), (443 : Vertex), (481 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex), (496 : Vertex), (499 : Vertex), (502 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (9 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (78 : Vertex), (102 : Vertex), (105 : Vertex), (111 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (166 : Vertex), (169 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (189 : Vertex), (190 : Vertex), (288 : Vertex), (294 : Vertex), (297 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (308 : Vertex), (317 : Vertex), (318 : Vertex), (354 : Vertex), (356 : Vertex), (359 : Vertex), (366 : Vertex), (373 : Vertex), (377 : Vertex), (378 : Vertex), (383 : Vertex), (417 : Vertex), (418 : Vertex), (420 : Vertex), (423 : Vertex), (424 : Vertex), (427 : Vertex), (430 : Vertex), (435 : Vertex), (437 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex), (480 : Vertex), (485 : Vertex), (486 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (504 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (7 : Vertex), (9 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (70 : Vertex), (78 : Vertex), (102 : Vertex), (105 : Vertex), (109 : Vertex), (111 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (171 : Vertex), (173 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (299 : Vertex), (301 : Vertex), (303 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (314 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (354 : Vertex), (356 : Vertex), (357 : Vertex), (358 : Vertex), (359 : Vertex), (361 : Vertex), (362 : Vertex), (364 : Vertex), (366 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (376 : Vertex), (377 : Vertex), (378 : Vertex), (379 : Vertex), (383 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (430 : Vertex), (431 : Vertex), (433 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (485 : Vertex), (486 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 504
def ban : Nat := 7525594226083836315247989486085173077543317616368698943467023840941544218256834614159562845377379948530496027591104280175609571560477658076206367434169660
def reachable : Nat := 5882213703858760784326035512120673049936048204223694434256537602780219811816712362642311452789523479159535830595381770678144311251468911870227281571914435
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
theorem evenSide_length : evenSide.length = 61 := by decide

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

end Snake9.Regrowth.E112189
