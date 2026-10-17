import RegrowthParityCounts
namespace Snake9.Regrowth.E112148
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 8, 12, 14, 6, 22, 23, 21, 5, 261, 269, 271, 287, 286, 284, 280, 272, 273, 275, 259, 258, 266, 394, 458, 450, 451, 467, 465, 464, 472, 476, 478, 479, 463, 461, 453, 452, 388, 420, 436, 444, 446, 447, 431, 427, 171, 187, 185, 184, 168, 172, 174, 166, 182, 183, 181, 165, 229, 237, 239, 255, 254, 252, 244, 240, 241, 243, 227, 226, 234, 106, 362, 354, 355, 371, 369, 368, 376, 380, 382, 383, 367, 365, 357, 356, 100, 102, 118, 119, 117, 125, 121, 105, 41, 45, 47, 39, 35, 51, 49, 48, 52, 60, 62, 58, 314, 315, 313, 317, 309, 311, 310]
def region : List Vertex := [(11 : Vertex), (25 : Vertex), (27 : Vertex), (65 : Vertex), (66 : Vertex), (67 : Vertex), (71 : Vertex), (75 : Vertex), (77 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (88 : Vertex), (90 : Vertex), (91 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (129 : Vertex), (130 : Vertex), (131 : Vertex), (135 : Vertex), (137 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (154 : Vertex), (156 : Vertex), (157 : Vertex), (158 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (203 : Vertex), (204 : Vertex), (206 : Vertex), (210 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (296 : Vertex), (300 : Vertex), (302 : Vertex), (310 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (331 : Vertex), (332 : Vertex), (334 : Vertex), (338 : Vertex), (340 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (349 : Vertex), (385 : Vertex), (391 : Vertex), (393 : Vertex), (402 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (409 : Vertex), (411 : Vertex), (413 : Vertex), (417 : Vertex), (418 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (492 : Vertex), (494 : Vertex), (498 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (509 : Vertex)]
def oddSide : List Vertex := [(11 : Vertex), (25 : Vertex), (67 : Vertex), (79 : Vertex), (81 : Vertex), (82 : Vertex), (84 : Vertex), (88 : Vertex), (91 : Vertex), (94 : Vertex), (131 : Vertex), (137 : Vertex), (143 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (157 : Vertex), (158 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (203 : Vertex), (206 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (289 : Vertex), (296 : Vertex), (302 : Vertex), (310 : Vertex), (321 : Vertex), (327 : Vertex), (328 : Vertex), (331 : Vertex), (334 : Vertex), (341 : Vertex), (342 : Vertex), (345 : Vertex), (346 : Vertex), (385 : Vertex), (391 : Vertex), (405 : Vertex), (406 : Vertex), (409 : Vertex), (433 : Vertex), (434 : Vertex), (481 : Vertex), (487 : Vertex), (488 : Vertex), (494 : Vertex), (501 : Vertex), (502 : Vertex), (505 : Vertex), (506 : Vertex)]
def evenSide : List Vertex := [(27 : Vertex), (65 : Vertex), (66 : Vertex), (71 : Vertex), (75 : Vertex), (77 : Vertex), (80 : Vertex), (83 : Vertex), (90 : Vertex), (92 : Vertex), (95 : Vertex), (129 : Vertex), (130 : Vertex), (135 : Vertex), (141 : Vertex), (144 : Vertex), (147 : Vertex), (154 : Vertex), (156 : Vertex), (159 : Vertex), (192 : Vertex), (198 : Vertex), (201 : Vertex), (204 : Vertex), (210 : Vertex), (215 : Vertex), (219 : Vertex), (221 : Vertex), (288 : Vertex), (294 : Vertex), (300 : Vertex), (320 : Vertex), (326 : Vertex), (329 : Vertex), (332 : Vertex), (338 : Vertex), (340 : Vertex), (343 : Vertex), (347 : Vertex), (349 : Vertex), (393 : Vertex), (402 : Vertex), (407 : Vertex), (411 : Vertex), (413 : Vertex), (417 : Vertex), (418 : Vertex), (435 : Vertex), (480 : Vertex), (486 : Vertex), (489 : Vertex), (492 : Vertex), (498 : Vertex), (503 : Vertex), (507 : Vertex), (509 : Vertex)]
def others : List Vertex := [(11 : Vertex), (25 : Vertex), (27 : Vertex), (65 : Vertex), (66 : Vertex), (67 : Vertex), (71 : Vertex), (75 : Vertex), (77 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (82 : Vertex), (83 : Vertex), (84 : Vertex), (88 : Vertex), (90 : Vertex), (91 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (129 : Vertex), (130 : Vertex), (131 : Vertex), (135 : Vertex), (137 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (154 : Vertex), (156 : Vertex), (157 : Vertex), (158 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (203 : Vertex), (204 : Vertex), (206 : Vertex), (210 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (288 : Vertex), (289 : Vertex), (294 : Vertex), (296 : Vertex), (300 : Vertex), (302 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (331 : Vertex), (332 : Vertex), (334 : Vertex), (338 : Vertex), (340 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (349 : Vertex), (385 : Vertex), (391 : Vertex), (393 : Vertex), (402 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (409 : Vertex), (411 : Vertex), (413 : Vertex), (417 : Vertex), (418 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (492 : Vertex), (494 : Vertex), (498 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (509 : Vertex)]
def head : Vertex := 310
def ban : Nat := 10951879686714352235775056642024935546012295484772796623405836103002868220159417934127766845966405436981563224618131793251385146108084637050756647524235263
def reachable : Nat := 2455928243228244863798968356180910581467070335819596754317725340718895809914129042674107452200497990708468633568354257602368736703861932895677001481848832
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
theorem evenSide_length : evenSide.length = 56 := by decide

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

end Snake9.Regrowth.E112148
