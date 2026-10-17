import RegrowthParityCounts
namespace Snake9.Regrowth.E112224
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 8, 72, 73, 65, 67, 83, 82, 80, 84, 92, 93, 95, 79, 78, 70, 6, 134, 142, 143, 159, 157, 156, 152, 144, 146, 147, 131, 129, 137, 393, 409, 411, 410, 394, 386, 384, 388, 404, 405, 407, 391, 455, 451, 467, 466, 464, 472, 456, 488, 232, 233, 225, 227, 243, 242, 240, 244, 252, 253, 255, 239, 238, 230, 486, 358, 366, 367, 383, 381, 380, 376, 368, 370, 371, 355, 353, 361, 297, 313, 315, 314, 298, 290, 288, 292, 308, 309, 311, 295, 39, 35, 51, 50, 48, 56, 60, 62, 30, 26, 27, 25, 17, 21, 5, 261, 257, 259, 267, 271, 287, 285]
def region : List Vertex := [(45 : Vertex), (96 : Vertex), (98 : Vertex), (100 : Vertex), (101 : Vertex), (106 : Vertex), (107 : Vertex), (108 : Vertex), (109 : Vertex), (113 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (160 : Vertex), (162 : Vertex), (164 : Vertex), (165 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (177 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (192 : Vertex), (194 : Vertex), (196 : Vertex), (197 : Vertex), (202 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (209 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (222 : Vertex), (268 : Vertex), (272 : Vertex), (274 : Vertex), (278 : Vertex), (280 : Vertex), (284 : Vertex), (285 : Vertex), (320 : Vertex), (322 : Vertex), (324 : Vertex), (330 : Vertex), (332 : Vertex), (333 : Vertex), (337 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (350 : Vertex), (417 : Vertex), (419 : Vertex), (421 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (430 : Vertex), (431 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (438 : Vertex), (440 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (447 : Vertex), (461 : Vertex), (462 : Vertex), (477 : Vertex), (478 : Vertex), (479 : Vertex), (485 : Vertex), (491 : Vertex), (493 : Vertex), (497 : Vertex), (501 : Vertex), (503 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(98 : Vertex), (100 : Vertex), (107 : Vertex), (109 : Vertex), (117 : Vertex), (118 : Vertex), (121 : Vertex), (122 : Vertex), (162 : Vertex), (164 : Vertex), (171 : Vertex), (173 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (194 : Vertex), (196 : Vertex), (203 : Vertex), (205 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (268 : Vertex), (274 : Vertex), (280 : Vertex), (285 : Vertex), (322 : Vertex), (324 : Vertex), (333 : Vertex), (341 : Vertex), (342 : Vertex), (345 : Vertex), (346 : Vertex), (419 : Vertex), (421 : Vertex), (428 : Vertex), (431 : Vertex), (433 : Vertex), (434 : Vertex), (440 : Vertex), (445 : Vertex), (446 : Vertex), (477 : Vertex), (478 : Vertex), (491 : Vertex), (493 : Vertex), (501 : Vertex), (505 : Vertex), (506 : Vertex)]
def evenSide : List Vertex := [(45 : Vertex), (96 : Vertex), (101 : Vertex), (106 : Vertex), (108 : Vertex), (113 : Vertex), (119 : Vertex), (123 : Vertex), (160 : Vertex), (165 : Vertex), (170 : Vertex), (172 : Vertex), (177 : Vertex), (183 : Vertex), (187 : Vertex), (192 : Vertex), (197 : Vertex), (202 : Vertex), (204 : Vertex), (209 : Vertex), (215 : Vertex), (219 : Vertex), (222 : Vertex), (272 : Vertex), (278 : Vertex), (284 : Vertex), (320 : Vertex), (330 : Vertex), (332 : Vertex), (337 : Vertex), (343 : Vertex), (347 : Vertex), (350 : Vertex), (417 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (432 : Vertex), (435 : Vertex), (438 : Vertex), (444 : Vertex), (447 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex), (485 : Vertex), (497 : Vertex), (503 : Vertex), (507 : Vertex), (510 : Vertex)]
def others : List Vertex := [(45 : Vertex), (96 : Vertex), (98 : Vertex), (100 : Vertex), (101 : Vertex), (106 : Vertex), (107 : Vertex), (108 : Vertex), (109 : Vertex), (113 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (160 : Vertex), (162 : Vertex), (164 : Vertex), (165 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (177 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (192 : Vertex), (194 : Vertex), (196 : Vertex), (197 : Vertex), (202 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (209 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (222 : Vertex), (268 : Vertex), (272 : Vertex), (274 : Vertex), (278 : Vertex), (280 : Vertex), (284 : Vertex), (320 : Vertex), (322 : Vertex), (324 : Vertex), (330 : Vertex), (332 : Vertex), (333 : Vertex), (337 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (350 : Vertex), (417 : Vertex), (419 : Vertex), (421 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (430 : Vertex), (431 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (438 : Vertex), (440 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (447 : Vertex), (461 : Vertex), (462 : Vertex), (477 : Vertex), (478 : Vertex), (479 : Vertex), (485 : Vertex), (491 : Vertex), (493 : Vertex), (497 : Vertex), (501 : Vertex), (503 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (510 : Vertex)]
def head : Vertex := 285
def ban : Nat := 9289441302050606918491361035204046946049427276494341589100618908618298609965659402502216644579560704834628981503115786508111200967060471870484303598059519
def reachable : Nat := 4118366627891990181082663963001799181429938544098051788622942535103465420107887574299657653587342722855402876683370264345642681844886098075949345408024576
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

end Snake9.Regrowth.E112224
