import RegrowthParityCounts
namespace Snake9.Regrowth.E112167
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[26, 27, 25, 17, 21, 5, 261, 257, 259, 267, 271, 287, 285, 284, 280, 272, 274, 278, 342, 343, 341, 337, 345, 347, 346, 330, 322, 320, 324, 332, 333, 461, 205, 204, 196, 192, 194, 202, 203, 219, 217, 209, 213, 215, 214, 222, 478, 510, 506, 507, 505, 497, 501, 485, 421, 417, 419, 427, 431, 447, 445, 444, 440, 432, 434, 438, 182, 183, 181, 177, 185, 187, 186, 170, 162, 160, 164, 172, 173, 45, 109, 108, 100, 96, 98, 106, 107, 123, 121, 113, 117, 119, 118, 126, 62, 60, 56, 48, 50, 51, 35, 39, 295, 311, 309, 308, 292, 288, 290, 298, 314, 315]
def region : List Vertex := [(0 : Vertex), (2 : Vertex), (6 : Vertex), (8 : Vertex), (12 : Vertex), (14 : Vertex), (65 : Vertex), (67 : Vertex), (70 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (78 : Vertex), (79 : Vertex), (80 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (88 : Vertex), (92 : Vertex), (93 : Vertex), (95 : Vertex), (129 : Vertex), (131 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (142 : Vertex), (143 : Vertex), (144 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (152 : Vertex), (156 : Vertex), (157 : Vertex), (159 : Vertex), (225 : Vertex), (227 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (238 : Vertex), (239 : Vertex), (240 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (248 : Vertex), (252 : Vertex), (253 : Vertex), (255 : Vertex), (297 : Vertex), (313 : Vertex), (315 : Vertex), (353 : Vertex), (355 : Vertex), (358 : Vertex), (360 : Vertex), (361 : Vertex), (366 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (371 : Vertex), (376 : Vertex), (380 : Vertex), (381 : Vertex), (383 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (398 : Vertex), (401 : Vertex), (403 : Vertex), (404 : Vertex), (405 : Vertex), (407 : Vertex), (409 : Vertex), (410 : Vertex), (411 : Vertex), (449 : Vertex), (451 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (464 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (472 : Vertex), (480 : Vertex), (482 : Vertex), (486 : Vertex), (488 : Vertex), (492 : Vertex)]
def oddSide : List Vertex := [(2 : Vertex), (8 : Vertex), (14 : Vertex), (67 : Vertex), (70 : Vertex), (73 : Vertex), (79 : Vertex), (82 : Vertex), (84 : Vertex), (88 : Vertex), (93 : Vertex), (131 : Vertex), (134 : Vertex), (137 : Vertex), (143 : Vertex), (146 : Vertex), (148 : Vertex), (152 : Vertex), (157 : Vertex), (227 : Vertex), (230 : Vertex), (233 : Vertex), (239 : Vertex), (242 : Vertex), (244 : Vertex), (248 : Vertex), (253 : Vertex), (313 : Vertex), (355 : Vertex), (358 : Vertex), (361 : Vertex), (367 : Vertex), (370 : Vertex), (376 : Vertex), (381 : Vertex), (386 : Vertex), (388 : Vertex), (391 : Vertex), (392 : Vertex), (398 : Vertex), (403 : Vertex), (405 : Vertex), (409 : Vertex), (410 : Vertex), (451 : Vertex), (454 : Vertex), (466 : Vertex), (468 : Vertex), (472 : Vertex), (482 : Vertex), (488 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (12 : Vertex), (65 : Vertex), (71 : Vertex), (72 : Vertex), (78 : Vertex), (80 : Vertex), (83 : Vertex), (92 : Vertex), (95 : Vertex), (129 : Vertex), (135 : Vertex), (136 : Vertex), (142 : Vertex), (144 : Vertex), (147 : Vertex), (156 : Vertex), (159 : Vertex), (225 : Vertex), (231 : Vertex), (232 : Vertex), (238 : Vertex), (240 : Vertex), (243 : Vertex), (252 : Vertex), (255 : Vertex), (297 : Vertex), (315 : Vertex), (353 : Vertex), (360 : Vertex), (366 : Vertex), (368 : Vertex), (371 : Vertex), (380 : Vertex), (383 : Vertex), (384 : Vertex), (390 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (401 : Vertex), (404 : Vertex), (407 : Vertex), (411 : Vertex), (449 : Vertex), (455 : Vertex), (456 : Vertex), (464 : Vertex), (467 : Vertex), (480 : Vertex), (486 : Vertex), (492 : Vertex)]
def others : List Vertex := [(0 : Vertex), (2 : Vertex), (6 : Vertex), (8 : Vertex), (12 : Vertex), (14 : Vertex), (65 : Vertex), (67 : Vertex), (70 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (78 : Vertex), (79 : Vertex), (80 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (88 : Vertex), (92 : Vertex), (93 : Vertex), (95 : Vertex), (129 : Vertex), (131 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (142 : Vertex), (143 : Vertex), (144 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (152 : Vertex), (156 : Vertex), (157 : Vertex), (159 : Vertex), (225 : Vertex), (227 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (238 : Vertex), (239 : Vertex), (240 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (248 : Vertex), (252 : Vertex), (253 : Vertex), (255 : Vertex), (297 : Vertex), (313 : Vertex), (353 : Vertex), (355 : Vertex), (358 : Vertex), (360 : Vertex), (361 : Vertex), (366 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (371 : Vertex), (376 : Vertex), (380 : Vertex), (381 : Vertex), (383 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (398 : Vertex), (401 : Vertex), (403 : Vertex), (404 : Vertex), (405 : Vertex), (407 : Vertex), (409 : Vertex), (410 : Vertex), (411 : Vertex), (449 : Vertex), (451 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (464 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (472 : Vertex), (480 : Vertex), (482 : Vertex), (486 : Vertex), (488 : Vertex), (492 : Vertex)]
def head : Vertex := 315
def ban : Nat := 13407794128678680100429134818210774834033057798508370377144296617528658289464933407216321961277596019447344046122414109961320630360839153106499714154475194
def reachable : Nat := 13801263916999144890179995071293446308022084023000579264826193105740608613569585552336889307408242687812064071940892433252451107416839933934851608901
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
theorem oddSide_length : oddSide.length = 51 := by decide
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

end Snake9.Regrowth.E112167
