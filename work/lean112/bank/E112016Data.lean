import RegrowthParityCounts
namespace Snake9.Regrowth.E112016
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 4, 68, 69, 77, 79, 95, 94, 92, 88, 80, 81, 83, 67, 66, 74, 10, 138, 130, 131, 147, 145, 144, 148, 156, 158, 159, 143, 141, 133, 389, 405, 407, 406, 390, 398, 396, 392, 408, 409, 411, 395, 459, 463, 479, 478, 476, 468, 464, 466, 210, 218, 219, 217, 221, 213, 215, 199, 198, 206, 204, 200, 192, 193, 449, 321, 320, 328, 332, 334, 326, 342, 343, 341, 349, 345, 347, 346, 282, 286, 284, 276, 272, 273, 275, 259, 263, 271, 269, 265, 9, 25, 29, 21, 23, 22, 18, 50, 48, 52, 60, 62, 63, 47, 43, 299, 315, 313, 312, 296, 300, 302]
def region : List Vertex := [(33 : Vertex), (37 : Vertex), (38 : Vertex), (96 : Vertex), (97 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (108 : Vertex), (110 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (161 : Vertex), (164 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (172 : Vertex), (174 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (239 : Vertex), (240 : Vertex), (241 : Vertex), (243 : Vertex), (244 : Vertex), (246 : Vertex), (248 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (289 : Vertex), (290 : Vertex), (293 : Vertex), (294 : Vertex), (302 : Vertex), (309 : Vertex), (310 : Vertex), (311 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (359 : Vertex), (361 : Vertex), (362 : Vertex), (365 : Vertex), (367 : Vertex), (368 : Vertex), (369 : Vertex), (370 : Vertex), (371 : Vertex), (372 : Vertex), (380 : Vertex), (382 : Vertex), (383 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (419 : Vertex), (420 : Vertex), (423 : Vertex), (425 : Vertex), (426 : Vertex), (429 : Vertex), (431 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (442 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (447 : Vertex), (480 : Vertex), (482 : Vertex), (483 : Vertex), (484 : Vertex), (485 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex), (493 : Vertex), (494 : Vertex), (497 : Vertex), (499 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (509 : Vertex)]
def oddSide : List Vertex := [(37 : Vertex), (38 : Vertex), (97 : Vertex), (103 : Vertex), (104 : Vertex), (110 : Vertex), (117 : Vertex), (118 : Vertex), (121 : Vertex), (122 : Vertex), (161 : Vertex), (164 : Vertex), (167 : Vertex), (168 : Vertex), (174 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (227 : Vertex), (229 : Vertex), (233 : Vertex), (234 : Vertex), (239 : Vertex), (241 : Vertex), (244 : Vertex), (248 : Vertex), (254 : Vertex), (289 : Vertex), (290 : Vertex), (302 : Vertex), (309 : Vertex), (310 : Vertex), (355 : Vertex), (357 : Vertex), (361 : Vertex), (362 : Vertex), (367 : Vertex), (369 : Vertex), (370 : Vertex), (372 : Vertex), (382 : Vertex), (416 : Vertex), (419 : Vertex), (425 : Vertex), (426 : Vertex), (431 : Vertex), (433 : Vertex), (434 : Vertex), (436 : Vertex), (445 : Vertex), (446 : Vertex), (482 : Vertex), (484 : Vertex), (487 : Vertex), (488 : Vertex), (493 : Vertex), (494 : Vertex), (499 : Vertex), (501 : Vertex), (502 : Vertex), (505 : Vertex), (506 : Vertex)]
def evenSide : List Vertex := [(33 : Vertex), (96 : Vertex), (102 : Vertex), (105 : Vertex), (108 : Vertex), (119 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (166 : Vertex), (169 : Vertex), (172 : Vertex), (183 : Vertex), (184 : Vertex), (187 : Vertex), (189 : Vertex), (226 : Vertex), (228 : Vertex), (235 : Vertex), (237 : Vertex), (240 : Vertex), (243 : Vertex), (246 : Vertex), (252 : Vertex), (255 : Vertex), (293 : Vertex), (294 : Vertex), (311 : Vertex), (354 : Vertex), (356 : Vertex), (359 : Vertex), (365 : Vertex), (368 : Vertex), (371 : Vertex), (380 : Vertex), (383 : Vertex), (417 : Vertex), (418 : Vertex), (420 : Vertex), (423 : Vertex), (429 : Vertex), (432 : Vertex), (435 : Vertex), (442 : Vertex), (444 : Vertex), (447 : Vertex), (480 : Vertex), (483 : Vertex), (485 : Vertex), (486 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex), (497 : Vertex), (503 : Vertex), (504 : Vertex), (507 : Vertex), (509 : Vertex)]
def others : List Vertex := [(33 : Vertex), (37 : Vertex), (38 : Vertex), (96 : Vertex), (97 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (108 : Vertex), (110 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (161 : Vertex), (164 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (172 : Vertex), (174 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (239 : Vertex), (240 : Vertex), (241 : Vertex), (243 : Vertex), (244 : Vertex), (246 : Vertex), (248 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (289 : Vertex), (290 : Vertex), (293 : Vertex), (294 : Vertex), (309 : Vertex), (310 : Vertex), (311 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (359 : Vertex), (361 : Vertex), (362 : Vertex), (365 : Vertex), (367 : Vertex), (368 : Vertex), (369 : Vertex), (370 : Vertex), (371 : Vertex), (372 : Vertex), (380 : Vertex), (382 : Vertex), (383 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (419 : Vertex), (420 : Vertex), (423 : Vertex), (425 : Vertex), (426 : Vertex), (429 : Vertex), (431 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (442 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (447 : Vertex), (480 : Vertex), (482 : Vertex), (483 : Vertex), (484 : Vertex), (485 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex), (493 : Vertex), (494 : Vertex), (497 : Vertex), (499 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (509 : Vertex)]
def head : Vertex := 302
def ban : Nat := 10898248964413997281448672909697317792590602791701554602911453366222076207393232351271698501994423485139681894345012285890687202450458465457315820500680703
def reachable : Nat := 2509558965528599818125352088508528334888763028890838774812108077499687822680314625530175796172479942550349963841473764963066680361488104489117828505403392
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
theorem oddSide_length : oddSide.length = 63 := by decide
theorem evenSide_length : evenSide.length = 58 := by decide

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

end Snake9.Regrowth.E112016
