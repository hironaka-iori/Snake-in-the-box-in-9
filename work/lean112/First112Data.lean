import RegrowthBridge
namespace Snake9.Regrowth.First112
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 17, 19, 18, 26, 30, 28, 29, 13, 15, 7, 6, 70, 78, 76, 72, 200, 192, 193, 209, 211, 210, 214, 222, 220, 221, 205, 207, 199, 455, 471, 469, 468, 452, 460, 462, 458, 474, 475, 473, 457, 393, 397, 413, 412, 414, 406, 402, 400, 144, 152, 153, 155, 159, 151, 149, 133, 132, 140, 142, 138, 130, 131, 387, 259, 258, 266, 270, 268, 260, 276, 277, 279, 287, 283, 281, 280, 344, 348, 350, 342, 338, 339, 337, 321, 325, 333, 335, 331, 75, 91, 95, 87, 85, 84, 80, 112, 114, 118, 126, 124, 125, 109, 105, 361, 377, 379, 378, 362, 366, 364]
def region : List Vertex := [(34 : Vertex), (35 : Vertex), (36 : Vertex), (37 : Vertex), (40 : Vertex), (42 : Vertex), (43 : Vertex), (44 : Vertex), (46 : Vertex), (52 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (59 : Vertex), (63 : Vertex), (99 : Vertex), (100 : Vertex), (103 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (171 : Vertex), (173 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (293 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (299 : Vertex), (301 : Vertex), (303 : Vertex), (304 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (352 : Vertex), (355 : Vertex), (356 : Vertex), (359 : Vertex), (364 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (430 : Vertex), (431 : Vertex), (433 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (483 : Vertex), (485 : Vertex), (486 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (504 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(35 : Vertex), (37 : Vertex), (42 : Vertex), (44 : Vertex), (52 : Vertex), (55 : Vertex), (56 : Vertex), (59 : Vertex), (100 : Vertex), (103 : Vertex), (161 : Vertex), (167 : Vertex), (168 : Vertex), (171 : Vertex), (173 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (227 : Vertex), (229 : Vertex), (230 : Vertex), (234 : Vertex), (236 : Vertex), (244 : Vertex), (247 : Vertex), (248 : Vertex), (251 : Vertex), (289 : Vertex), (295 : Vertex), (296 : Vertex), (299 : Vertex), (301 : Vertex), (304 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (352 : Vertex), (355 : Vertex), (364 : Vertex), (372 : Vertex), (375 : Vertex), (416 : Vertex), (421 : Vertex), (422 : Vertex), (426 : Vertex), (428 : Vertex), (431 : Vertex), (433 : Vertex), (436 : Vertex), (439 : Vertex), (440 : Vertex), (443 : Vertex), (481 : Vertex), (482 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex), (496 : Vertex), (499 : Vertex), (502 : Vertex), (508 : Vertex), (511 : Vertex)]
def others : List Vertex := [(34 : Vertex), (35 : Vertex), (36 : Vertex), (37 : Vertex), (40 : Vertex), (42 : Vertex), (43 : Vertex), (44 : Vertex), (46 : Vertex), (52 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (59 : Vertex), (63 : Vertex), (99 : Vertex), (100 : Vertex), (103 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (171 : Vertex), (173 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (250 : Vertex), (251 : Vertex), (255 : Vertex), (288 : Vertex), (289 : Vertex), (293 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (299 : Vertex), (301 : Vertex), (303 : Vertex), (304 : Vertex), (305 : Vertex), (306 : Vertex), (307 : Vertex), (310 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (352 : Vertex), (355 : Vertex), (356 : Vertex), (359 : Vertex), (372 : Vertex), (373 : Vertex), (375 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (430 : Vertex), (431 : Vertex), (433 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (482 : Vertex), (483 : Vertex), (485 : Vertex), (486 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (496 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (504 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex), (511 : Vertex)]
def head : Vertex := 364
def ban : Nat := 769315973925216891748859175253841669872182681560898349386418134583636011493331450945039444877863364827942167912616278639453308262382251545060940177211391
def reachable : Nat := 12638491956017380207825165822952004457607183139031495028337143309138128018580215525856834853289040062862089690273869772214300574549564318401372708828872704
theorem ban_eq : banFrom (fun i => pre[i]!) 111 = ban := by decide
theorem head_eq : pre[111]! = head.val := by decide
theorem region_closed : expand reachable &&& freeOf ban = reachable := by decide
theorem region_start : ∀ y : Fin 512,
    (expand (2^head.val) &&& freeOf ban).testBit y.val = true →
    reachable.testBit y.val = true := by decide
theorem region_mem : ∀ v : Vertex,
    v = head ∨ reachable.testBit v.val = true → v ∈ region := by decide
theorem odd_mem : ∀ v : Vertex, v ∈ region → bitParity v.val = true → v ∈ oddSide := by decide
theorem others_mem : ∀ v : Vertex, v ∈ region → v ≠ head → v ∈ others := by decide
theorem others_nodup : others.Nodup := by decide
theorem head_not_others : head ∉ others := by decide
theorem oddSide_length : oddSide.length = 63 := by decide

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

end Snake9.Regrowth.First112
