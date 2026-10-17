import RegrowthParityCounts
namespace Snake9.Regrowth.E112256
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 4, 36, 38, 166, 162, 178, 50, 18, 22, 150, 158, 142, 14, 10, 42, 40, 168, 172, 188, 60, 28, 24, 152, 144, 145, 17, 21, 53, 55, 183, 191, 175, 47, 45, 13, 141, 133, 165, 161, 33, 35, 3, 131, 139, 155, 27, 59, 57, 185, 441, 433, 305, 307, 275, 279, 407, 415, 399, 271, 267, 299, 427, 419, 423, 295, 293, 261, 257, 385, 393, 392, 264, 268, 300, 302, 430, 446, 438, 310, 308, 276, 404, 388, 420, 416, 288, 290, 258, 386, 402, 410, 282, 314, 312, 376, 360, 488, 489, 481, 353, 355, 323, 327, 455, 454, 486, 358, 356, 324, 320, 336]
def region : List Vertex := [(65 : Vertex), (66 : Vertex), (69 : Vertex), (70 : Vertex), (72 : Vertex), (73 : Vertex), (75 : Vertex), (76 : Vertex), (79 : Vertex), (80 : Vertex), (83 : Vertex), (84 : Vertex), (87 : Vertex), (89 : Vertex), (90 : Vertex), (93 : Vertex), (94 : Vertex), (95 : Vertex), (96 : Vertex), (98 : Vertex), (101 : Vertex), (103 : Vertex), (105 : Vertex), (107 : Vertex), (108 : Vertex), (110 : Vertex), (112 : Vertex), (113 : Vertex), (115 : Vertex), (116 : Vertex), (118 : Vertex), (122 : Vertex), (125 : Vertex), (126 : Vertex), (127 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (196 : Vertex), (200 : Vertex), (201 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (210 : Vertex), (211 : Vertex), (212 : Vertex), (213 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (223 : Vertex), (224 : Vertex), (227 : Vertex), (228 : Vertex), (231 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (238 : Vertex), (240 : Vertex), (241 : Vertex), (243 : Vertex), (244 : Vertex), (245 : Vertex), (246 : Vertex), (248 : Vertex), (250 : Vertex), (251 : Vertex), (253 : Vertex), (254 : Vertex), (281 : Vertex), (285 : Vertex), (317 : Vertex), (319 : Vertex), (329 : Vertex), (330 : Vertex), (333 : Vertex), (334 : Vertex), (336 : Vertex), (337 : Vertex), (338 : Vertex), (341 : Vertex), (342 : Vertex), (345 : Vertex), (347 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (351 : Vertex), (365 : Vertex), (367 : Vertex), (370 : Vertex), (373 : Vertex), (375 : Vertex), (379 : Vertex), (381 : Vertex), (382 : Vertex), (383 : Vertex), (458 : Vertex), (459 : Vertex), (460 : Vertex), (461 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (469 : Vertex), (472 : Vertex), (473 : Vertex), (475 : Vertex), (476 : Vertex), (477 : Vertex), (478 : Vertex), (495 : Vertex), (496 : Vertex), (498 : Vertex), (499 : Vertex), (500 : Vertex), (501 : Vertex), (503 : Vertex), (506 : Vertex), (507 : Vertex), (508 : Vertex), (509 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(69 : Vertex), (70 : Vertex), (73 : Vertex), (76 : Vertex), (79 : Vertex), (84 : Vertex), (87 : Vertex), (93 : Vertex), (94 : Vertex), (98 : Vertex), (103 : Vertex), (107 : Vertex), (110 : Vertex), (112 : Vertex), (115 : Vertex), (118 : Vertex), (122 : Vertex), (127 : Vertex), (193 : Vertex), (194 : Vertex), (196 : Vertex), (200 : Vertex), (211 : Vertex), (213 : Vertex), (217 : Vertex), (218 : Vertex), (220 : Vertex), (223 : Vertex), (224 : Vertex), (227 : Vertex), (234 : Vertex), (241 : Vertex), (244 : Vertex), (248 : Vertex), (251 : Vertex), (253 : Vertex), (254 : Vertex), (285 : Vertex), (319 : Vertex), (333 : Vertex), (334 : Vertex), (336 : Vertex), (341 : Vertex), (342 : Vertex), (345 : Vertex), (348 : Vertex), (351 : Vertex), (367 : Vertex), (370 : Vertex), (375 : Vertex), (379 : Vertex), (381 : Vertex), (382 : Vertex), (458 : Vertex), (460 : Vertex), (465 : Vertex), (472 : Vertex), (475 : Vertex), (477 : Vertex), (478 : Vertex), (496 : Vertex), (499 : Vertex), (501 : Vertex), (506 : Vertex), (508 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(65 : Vertex), (66 : Vertex), (72 : Vertex), (75 : Vertex), (80 : Vertex), (83 : Vertex), (89 : Vertex), (90 : Vertex), (95 : Vertex), (96 : Vertex), (101 : Vertex), (105 : Vertex), (108 : Vertex), (113 : Vertex), (116 : Vertex), (125 : Vertex), (126 : Vertex), (192 : Vertex), (201 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (210 : Vertex), (212 : Vertex), (215 : Vertex), (221 : Vertex), (228 : Vertex), (231 : Vertex), (235 : Vertex), (237 : Vertex), (238 : Vertex), (240 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (250 : Vertex), (281 : Vertex), (317 : Vertex), (329 : Vertex), (330 : Vertex), (337 : Vertex), (338 : Vertex), (347 : Vertex), (349 : Vertex), (350 : Vertex), (365 : Vertex), (373 : Vertex), (383 : Vertex), (459 : Vertex), (461 : Vertex), (464 : Vertex), (467 : Vertex), (469 : Vertex), (473 : Vertex), (476 : Vertex), (495 : Vertex), (498 : Vertex), (500 : Vertex), (503 : Vertex), (507 : Vertex), (509 : Vertex)]
def others : List Vertex := [(65 : Vertex), (66 : Vertex), (69 : Vertex), (70 : Vertex), (72 : Vertex), (73 : Vertex), (75 : Vertex), (76 : Vertex), (79 : Vertex), (80 : Vertex), (83 : Vertex), (84 : Vertex), (87 : Vertex), (89 : Vertex), (90 : Vertex), (93 : Vertex), (94 : Vertex), (95 : Vertex), (96 : Vertex), (98 : Vertex), (101 : Vertex), (103 : Vertex), (105 : Vertex), (107 : Vertex), (108 : Vertex), (110 : Vertex), (112 : Vertex), (113 : Vertex), (115 : Vertex), (116 : Vertex), (118 : Vertex), (122 : Vertex), (125 : Vertex), (126 : Vertex), (127 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (196 : Vertex), (200 : Vertex), (201 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (210 : Vertex), (211 : Vertex), (212 : Vertex), (213 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (223 : Vertex), (224 : Vertex), (227 : Vertex), (228 : Vertex), (231 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (238 : Vertex), (240 : Vertex), (241 : Vertex), (243 : Vertex), (244 : Vertex), (245 : Vertex), (246 : Vertex), (248 : Vertex), (250 : Vertex), (251 : Vertex), (253 : Vertex), (254 : Vertex), (281 : Vertex), (285 : Vertex), (317 : Vertex), (319 : Vertex), (329 : Vertex), (330 : Vertex), (333 : Vertex), (334 : Vertex), (337 : Vertex), (338 : Vertex), (341 : Vertex), (342 : Vertex), (345 : Vertex), (347 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (351 : Vertex), (365 : Vertex), (367 : Vertex), (370 : Vertex), (373 : Vertex), (375 : Vertex), (379 : Vertex), (381 : Vertex), (382 : Vertex), (383 : Vertex), (458 : Vertex), (459 : Vertex), (460 : Vertex), (461 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (469 : Vertex), (472 : Vertex), (473 : Vertex), (475 : Vertex), (476 : Vertex), (477 : Vertex), (478 : Vertex), (495 : Vertex), (496 : Vertex), (498 : Vertex), (499 : Vertex), (500 : Vertex), (501 : Vertex), (503 : Vertex), (506 : Vertex), (507 : Vertex), (508 : Vertex), (509 : Vertex), (511 : Vertex)]
def head : Vertex := 336
def ban : Nat := 3522679759876770369860614428991614567235358148935054994365108739429841667211511111323405329082258820234011239645166644633328643561016247336836997975113727
def reachable : Nat := 9885128170065826729713409182879384499836577882450246311816600986073384674953748280238678661773990704643209098554116354150636190555324841907810736543891456
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
theorem oddSide_length : oddSide.length = 66 := by decide
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

end Snake9.Regrowth.E112256
