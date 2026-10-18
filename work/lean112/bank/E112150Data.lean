import RegrowthParityCounts
namespace Snake9.Regrowth.E112150
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 2, 18, 274, 278, 276, 284, 280, 264, 266, 267, 271, 263, 261, 257, 321, 320, 322, 326, 334, 332, 333, 349, 341, 343, 339, 347, 346, 474, 218, 219, 211, 215, 213, 221, 220, 204, 206, 198, 194, 192, 193, 201, 457, 489, 493, 492, 494, 486, 482, 498, 434, 438, 436, 444, 440, 424, 426, 427, 431, 423, 421, 417, 161, 160, 162, 166, 174, 172, 173, 189, 181, 183, 179, 187, 186, 58, 122, 123, 115, 119, 117, 125, 124, 108, 110, 102, 98, 96, 97, 105, 41, 43, 47, 39, 37, 36, 52, 48, 304, 288, 290, 291, 307, 311, 309, 317, 301, 300, 302, 318, 382]
def region : List Vertex := [(12 : Vertex), (13 : Vertex), (14 : Vertex), (17 : Vertex), (21 : Vertex), (23 : Vertex), (25 : Vertex), (27 : Vertex), (29 : Vertex), (30 : Vertex), (31 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (71 : Vertex), (72 : Vertex), (74 : Vertex), (75 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (84 : Vertex), (86 : Vertex), (88 : Vertex), (89 : Vertex), (94 : Vertex), (95 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (135 : Vertex), (136 : Vertex), (138 : Vertex), (139 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (148 : Vertex), (150 : Vertex), (152 : Vertex), (153 : Vertex), (158 : Vertex), (159 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (231 : Vertex), (232 : Vertex), (234 : Vertex), (235 : Vertex), (239 : Vertex), (240 : Vertex), (241 : Vertex), (244 : Vertex), (246 : Vertex), (248 : Vertex), (249 : Vertex), (254 : Vertex), (255 : Vertex), (356 : Vertex), (357 : Vertex), (359 : Vertex), (360 : Vertex), (362 : Vertex), (363 : Vertex), (367 : Vertex), (369 : Vertex), (372 : Vertex), (374 : Vertex), (376 : Vertex), (377 : Vertex), (382 : Vertex), (383 : Vertex), (384 : Vertex), (386 : Vertex), (387 : Vertex), (388 : Vertex), (390 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (400 : Vertex), (401 : Vertex), (403 : Vertex), (405 : Vertex), (407 : Vertex), (409 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex), (415 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (455 : Vertex), (463 : Vertex), (464 : Vertex), (465 : Vertex), (468 : Vertex), (470 : Vertex), (479 : Vertex), (497 : Vertex), (501 : Vertex), (503 : Vertex), (507 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(13 : Vertex), (14 : Vertex), (21 : Vertex), (25 : Vertex), (31 : Vertex), (67 : Vertex), (69 : Vertex), (74 : Vertex), (79 : Vertex), (81 : Vertex), (84 : Vertex), (88 : Vertex), (94 : Vertex), (131 : Vertex), (133 : Vertex), (138 : Vertex), (143 : Vertex), (145 : Vertex), (148 : Vertex), (152 : Vertex), (158 : Vertex), (227 : Vertex), (229 : Vertex), (234 : Vertex), (239 : Vertex), (241 : Vertex), (244 : Vertex), (248 : Vertex), (254 : Vertex), (357 : Vertex), (362 : Vertex), (367 : Vertex), (369 : Vertex), (372 : Vertex), (376 : Vertex), (382 : Vertex), (386 : Vertex), (388 : Vertex), (397 : Vertex), (398 : Vertex), (400 : Vertex), (403 : Vertex), (405 : Vertex), (409 : Vertex), (415 : Vertex), (451 : Vertex), (453 : Vertex), (463 : Vertex), (465 : Vertex), (468 : Vertex), (501 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(12 : Vertex), (17 : Vertex), (23 : Vertex), (27 : Vertex), (29 : Vertex), (30 : Vertex), (68 : Vertex), (71 : Vertex), (72 : Vertex), (75 : Vertex), (80 : Vertex), (86 : Vertex), (89 : Vertex), (95 : Vertex), (132 : Vertex), (135 : Vertex), (136 : Vertex), (139 : Vertex), (144 : Vertex), (150 : Vertex), (153 : Vertex), (159 : Vertex), (228 : Vertex), (231 : Vertex), (232 : Vertex), (235 : Vertex), (240 : Vertex), (246 : Vertex), (249 : Vertex), (255 : Vertex), (356 : Vertex), (359 : Vertex), (360 : Vertex), (363 : Vertex), (374 : Vertex), (377 : Vertex), (383 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (396 : Vertex), (401 : Vertex), (407 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex), (452 : Vertex), (455 : Vertex), (464 : Vertex), (470 : Vertex), (479 : Vertex), (497 : Vertex), (503 : Vertex), (507 : Vertex)]
def others : List Vertex := [(12 : Vertex), (13 : Vertex), (14 : Vertex), (17 : Vertex), (21 : Vertex), (23 : Vertex), (25 : Vertex), (27 : Vertex), (29 : Vertex), (30 : Vertex), (31 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (71 : Vertex), (72 : Vertex), (74 : Vertex), (75 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (84 : Vertex), (86 : Vertex), (88 : Vertex), (89 : Vertex), (94 : Vertex), (95 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (135 : Vertex), (136 : Vertex), (138 : Vertex), (139 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (148 : Vertex), (150 : Vertex), (152 : Vertex), (153 : Vertex), (158 : Vertex), (159 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (231 : Vertex), (232 : Vertex), (234 : Vertex), (235 : Vertex), (239 : Vertex), (240 : Vertex), (241 : Vertex), (244 : Vertex), (246 : Vertex), (248 : Vertex), (249 : Vertex), (254 : Vertex), (255 : Vertex), (356 : Vertex), (357 : Vertex), (359 : Vertex), (360 : Vertex), (362 : Vertex), (363 : Vertex), (367 : Vertex), (369 : Vertex), (372 : Vertex), (374 : Vertex), (376 : Vertex), (377 : Vertex), (383 : Vertex), (384 : Vertex), (386 : Vertex), (387 : Vertex), (388 : Vertex), (390 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (400 : Vertex), (401 : Vertex), (403 : Vertex), (405 : Vertex), (407 : Vertex), (409 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex), (415 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (455 : Vertex), (463 : Vertex), (464 : Vertex), (465 : Vertex), (468 : Vertex), (470 : Vertex), (479 : Vertex), (497 : Vertex), (501 : Vertex), (503 : Vertex), (507 : Vertex), (511 : Vertex)]
def head : Vertex := 382
def ban : Nat := 6251766885690792097525060305410564779518945791744111144405342652767094813518196897878300808991147691200119330929247284930033006494531228783465604004548607
def reachable : Nat := 7156041044251805002048964692795281347960420028848282233318218790954669216555350078923573489175755736489912527257238765923720876317415341162968045001535488
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
theorem oddSide_length : oddSide.length = 52 := by decide
theorem evenSide_length : evenSide.length = 54 := by decide

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

end Snake9.Regrowth.E112150
