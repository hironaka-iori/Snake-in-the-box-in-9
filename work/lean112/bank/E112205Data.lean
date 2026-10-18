import RegrowthParityCounts
namespace Snake9.Regrowth.E112205
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[472, 473, 475, 479, 471, 469, 468, 452, 460, 462, 458, 450, 451, 195, 67, 66, 74, 78, 76, 68, 69, 85, 87, 95, 91, 89, 88, 80, 208, 210, 214, 222, 220, 221, 205, 201, 137, 153, 155, 154, 138, 142, 140, 132, 148, 149, 151, 135, 391, 399, 397, 413, 412, 414, 406, 402, 403, 401, 385, 384, 392, 264, 328, 320, 321, 337, 339, 338, 346, 350, 348, 349, 333, 335, 327, 326, 262, 294, 310, 318, 316, 317, 301, 297, 41, 57, 59, 58, 42, 46, 44, 36, 52, 53, 55, 39, 103, 111, 109, 125, 124, 126, 118, 114, 115, 113, 97, 96, 104, 232, 488, 480]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (11 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (163 : Vertex), (165 : Vertex), (166 : Vertex), (171 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (184 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (191 : Vertex), (226 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (235 : Vertex), (238 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (255 : Vertex), (259 : Vertex), (261 : Vertex), (267 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (288 : Vertex), (291 : Vertex), (304 : Vertex), (305 : Vertex), (307 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (362 : Vertex), (363 : Vertex), (364 : Vertex), (366 : Vertex), (368 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (376 : Vertex), (377 : Vertex), (379 : Vertex), (383 : Vertex), (418 : Vertex), (419 : Vertex), (420 : Vertex), (421 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (430 : Vertex), (432 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (485 : Vertex), (486 : Vertex), (487 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (11 : Vertex), (13 : Vertex), (19 : Vertex), (22 : Vertex), (28 : Vertex), (161 : Vertex), (162 : Vertex), (171 : Vertex), (173 : Vertex), (176 : Vertex), (179 : Vertex), (182 : Vertex), (188 : Vertex), (191 : Vertex), (229 : Vertex), (230 : Vertex), (244 : Vertex), (247 : Vertex), (251 : Vertex), (259 : Vertex), (261 : Vertex), (276 : Vertex), (279 : Vertex), (283 : Vertex), (304 : Vertex), (307 : Vertex), (355 : Vertex), (357 : Vertex), (362 : Vertex), (364 : Vertex), (372 : Vertex), (375 : Vertex), (376 : Vertex), (379 : Vertex), (419 : Vertex), (421 : Vertex), (426 : Vertex), (428 : Vertex), (436 : Vertex), (439 : Vertex), (440 : Vertex), (443 : Vertex), (481 : Vertex), (487 : Vertex), (491 : Vertex), (493 : Vertex), (496 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (29 : Vertex), (30 : Vertex), (160 : Vertex), (163 : Vertex), (165 : Vertex), (166 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (184 : Vertex), (189 : Vertex), (190 : Vertex), (226 : Vertex), (228 : Vertex), (235 : Vertex), (238 : Vertex), (245 : Vertex), (249 : Vertex), (250 : Vertex), (255 : Vertex), (267 : Vertex), (272 : Vertex), (277 : Vertex), (281 : Vertex), (287 : Vertex), (288 : Vertex), (291 : Vertex), (305 : Vertex), (354 : Vertex), (356 : Vertex), (363 : Vertex), (366 : Vertex), (368 : Vertex), (373 : Vertex), (377 : Vertex), (383 : Vertex), (418 : Vertex), (420 : Vertex), (427 : Vertex), (430 : Vertex), (432 : Vertex), (437 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex), (480 : Vertex), (485 : Vertex), (486 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (11 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (163 : Vertex), (165 : Vertex), (166 : Vertex), (171 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (184 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (191 : Vertex), (226 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (235 : Vertex), (238 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (255 : Vertex), (259 : Vertex), (261 : Vertex), (267 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (288 : Vertex), (291 : Vertex), (304 : Vertex), (305 : Vertex), (307 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (362 : Vertex), (363 : Vertex), (364 : Vertex), (366 : Vertex), (368 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (376 : Vertex), (377 : Vertex), (379 : Vertex), (383 : Vertex), (418 : Vertex), (419 : Vertex), (420 : Vertex), (421 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (430 : Vertex), (432 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (481 : Vertex), (485 : Vertex), (486 : Vertex), (487 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 480
def ban : Nat := 7316097629884046226330248630131661274649698099385588849645649705358917499607958765044825346914547409448536831234082808749293202706026239886153506763134972
def reachable : Nat := 6091710300058550873243776368074184852829667721206804528077911738362846530465588211757048951252356018241495026952403242104460680105920330060280142242949123
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

end Snake9.Regrowth.E112205
