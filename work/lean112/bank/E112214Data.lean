import RegrowthParityCounts
namespace Snake9.Regrowth.E112214
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 257, 265, 264, 266, 282, 283, 287, 285, 277, 276, 260, 262, 263, 7, 15, 13, 12, 28, 24, 88, 72, 74, 78, 70, 68, 69, 85, 93, 95, 91, 83, 82, 18, 146, 147, 155, 159, 157, 149, 133, 132, 134, 142, 138, 136, 137, 201, 205, 207, 199, 195, 194, 192, 208, 212, 220, 222, 218, 474, 458, 462, 454, 452, 453, 449, 481, 417, 425, 424, 426, 430, 422, 420, 436, 437, 445, 447, 443, 435, 434, 498, 370, 371, 379, 383, 381, 373, 357, 356, 358, 366, 362, 360, 361, 105, 109, 111, 103, 99, 98, 96, 112, 116, 124, 126, 122, 58, 42, 46, 38]
def region : List Vertex := [(36 : Vertex), (37 : Vertex), (38 : Vertex), (49 : Vertex), (51 : Vertex), (53 : Vertex), (54 : Vertex), (55 : Vertex), (57 : Vertex), (61 : Vertex), (63 : Vertex), (160 : Vertex), (162 : Vertex), (163 : Vertex), (167 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (188 : Vertex), (190 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (232 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (241 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (253 : Vertex), (255 : Vertex), (288 : Vertex), (290 : Vertex), (291 : Vertex), (299 : Vertex), (300 : Vertex), (301 : Vertex), (303 : Vertex), (304 : Vertex), (305 : Vertex), (310 : Vertex), (311 : Vertex), (312 : Vertex), (313 : Vertex), (316 : Vertex), (318 : Vertex), (320 : Vertex), (322 : Vertex), (323 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (348 : Vertex), (350 : Vertex), (384 : Vertex), (386 : Vertex), (387 : Vertex), (395 : Vertex), (396 : Vertex), (397 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (412 : Vertex), (414 : Vertex), (467 : Vertex), (471 : Vertex), (473 : Vertex), (477 : Vertex), (479 : Vertex), (487 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (495 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (508 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(37 : Vertex), (38 : Vertex), (49 : Vertex), (55 : Vertex), (61 : Vertex), (162 : Vertex), (167 : Vertex), (171 : Vertex), (173 : Vertex), (176 : Vertex), (182 : Vertex), (185 : Vertex), (188 : Vertex), (229 : Vertex), (230 : Vertex), (234 : Vertex), (236 : Vertex), (241 : Vertex), (247 : Vertex), (248 : Vertex), (251 : Vertex), (253 : Vertex), (290 : Vertex), (299 : Vertex), (301 : Vertex), (304 : Vertex), (310 : Vertex), (313 : Vertex), (316 : Vertex), (322 : Vertex), (331 : Vertex), (333 : Vertex), (336 : Vertex), (342 : Vertex), (345 : Vertex), (348 : Vertex), (386 : Vertex), (395 : Vertex), (397 : Vertex), (400 : Vertex), (406 : Vertex), (409 : Vertex), (412 : Vertex), (471 : Vertex), (477 : Vertex), (487 : Vertex), (491 : Vertex), (493 : Vertex), (505 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(36 : Vertex), (51 : Vertex), (53 : Vertex), (54 : Vertex), (57 : Vertex), (63 : Vertex), (160 : Vertex), (163 : Vertex), (172 : Vertex), (175 : Vertex), (177 : Vertex), (183 : Vertex), (184 : Vertex), (190 : Vertex), (228 : Vertex), (232 : Vertex), (235 : Vertex), (238 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (249 : Vertex), (255 : Vertex), (288 : Vertex), (291 : Vertex), (300 : Vertex), (303 : Vertex), (305 : Vertex), (311 : Vertex), (312 : Vertex), (318 : Vertex), (320 : Vertex), (323 : Vertex), (332 : Vertex), (335 : Vertex), (337 : Vertex), (343 : Vertex), (350 : Vertex), (384 : Vertex), (387 : Vertex), (396 : Vertex), (399 : Vertex), (401 : Vertex), (407 : Vertex), (408 : Vertex), (414 : Vertex), (467 : Vertex), (473 : Vertex), (479 : Vertex), (492 : Vertex), (495 : Vertex), (503 : Vertex), (504 : Vertex), (510 : Vertex)]
def others : List Vertex := [(36 : Vertex), (37 : Vertex), (49 : Vertex), (51 : Vertex), (53 : Vertex), (54 : Vertex), (55 : Vertex), (57 : Vertex), (61 : Vertex), (63 : Vertex), (160 : Vertex), (162 : Vertex), (163 : Vertex), (167 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (188 : Vertex), (190 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (232 : Vertex), (234 : Vertex), (235 : Vertex), (236 : Vertex), (238 : Vertex), (241 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (251 : Vertex), (253 : Vertex), (255 : Vertex), (288 : Vertex), (290 : Vertex), (291 : Vertex), (299 : Vertex), (300 : Vertex), (301 : Vertex), (303 : Vertex), (304 : Vertex), (305 : Vertex), (310 : Vertex), (311 : Vertex), (312 : Vertex), (313 : Vertex), (316 : Vertex), (318 : Vertex), (320 : Vertex), (322 : Vertex), (323 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (348 : Vertex), (350 : Vertex), (384 : Vertex), (386 : Vertex), (387 : Vertex), (395 : Vertex), (396 : Vertex), (397 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (412 : Vertex), (414 : Vertex), (467 : Vertex), (471 : Vertex), (473 : Vertex), (477 : Vertex), (479 : Vertex), (487 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (495 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (508 : Vertex), (510 : Vertex)]
def head : Vertex := 38
def ban : Nat := 9034410629383863293836072696194926525698317575962992409842629554732622339489476110429610373016625568050375607896032384023202347663682509924518589055893503
def reachable : Nat := 4373397300558733805737952302010919601781048244629400967880931888989141690584070866372263925150277859639656250290453666830551535148264060021915059950190592
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
theorem oddSide_length : oddSide.length = 50 := by decide
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

end Snake9.Regrowth.E112214
