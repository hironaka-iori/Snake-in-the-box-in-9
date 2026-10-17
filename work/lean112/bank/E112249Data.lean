import RegrowthParityCounts
namespace Snake9.Regrowth.E112249
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[88, 89, 91, 95, 87, 85, 84, 68, 76, 78, 74, 66, 67, 323, 451, 450, 458, 462, 460, 452, 453, 469, 471, 479, 475, 473, 472, 464, 336, 368, 372, 373, 375, 383, 379, 363, 299, 303, 301, 293, 289, 305, 307, 306, 310, 318, 316, 312, 56, 57, 59, 63, 55, 53, 52, 36, 44, 46, 42, 34, 35, 163, 227, 226, 234, 238, 236, 228, 229, 245, 247, 255, 251, 249, 248, 240, 176, 144, 148, 149, 151, 159, 155, 139, 395, 399, 397, 413, 412, 414, 406, 402, 403, 401, 385, 384, 392, 136, 200, 192, 193, 209, 211, 210, 218, 222, 220, 221, 205, 207, 199, 198]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (5 : Vertex), (6 : Vertex), (7 : Vertex), (9 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (96 : Vertex), (97 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (109 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (130 : Vertex), (134 : Vertex), (142 : Vertex), (166 : Vertex), (169 : Vertex), (173 : Vertex), (175 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (198 : Vertex), (258 : Vertex), (260 : Vertex), (262 : Vertex), (263 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (270 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (287 : Vertex), (326 : Vertex), (328 : Vertex), (329 : Vertex), (333 : Vertex), (335 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (354 : Vertex), (358 : Vertex), (360 : Vertex), (364 : Vertex), (366 : Vertex), (418 : Vertex), (420 : Vertex), (422 : Vertex), (423 : Vertex), (425 : Vertex), (426 : Vertex), (428 : Vertex), (430 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (13 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (97 : Vertex), (103 : Vertex), (104 : Vertex), (109 : Vertex), (115 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (134 : Vertex), (173 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (276 : Vertex), (279 : Vertex), (283 : Vertex), (328 : Vertex), (333 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (358 : Vertex), (364 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (428 : Vertex), (436 : Vertex), (439 : Vertex), (443 : Vertex), (481 : Vertex), (487 : Vertex), (488 : Vertex), (493 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (5 : Vertex), (6 : Vertex), (9 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (29 : Vertex), (30 : Vertex), (96 : Vertex), (102 : Vertex), (105 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (125 : Vertex), (126 : Vertex), (130 : Vertex), (142 : Vertex), (166 : Vertex), (169 : Vertex), (175 : Vertex), (189 : Vertex), (190 : Vertex), (198 : Vertex), (258 : Vertex), (260 : Vertex), (263 : Vertex), (270 : Vertex), (277 : Vertex), (281 : Vertex), (282 : Vertex), (287 : Vertex), (326 : Vertex), (329 : Vertex), (335 : Vertex), (349 : Vertex), (350 : Vertex), (354 : Vertex), (360 : Vertex), (366 : Vertex), (418 : Vertex), (420 : Vertex), (423 : Vertex), (430 : Vertex), (437 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex), (480 : Vertex), (486 : Vertex), (489 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (5 : Vertex), (6 : Vertex), (7 : Vertex), (9 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (96 : Vertex), (97 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (109 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (115 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (130 : Vertex), (134 : Vertex), (142 : Vertex), (166 : Vertex), (169 : Vertex), (173 : Vertex), (175 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (258 : Vertex), (260 : Vertex), (262 : Vertex), (263 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (270 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (287 : Vertex), (326 : Vertex), (328 : Vertex), (329 : Vertex), (333 : Vertex), (335 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (354 : Vertex), (358 : Vertex), (360 : Vertex), (364 : Vertex), (366 : Vertex), (418 : Vertex), (420 : Vertex), (422 : Vertex), (423 : Vertex), (425 : Vertex), (426 : Vertex), (428 : Vertex), (430 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (447 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (489 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (498 : Vertex), (499 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 198
def ban : Nat := 7316306309409389199465790334422011422395125189736201615391091259197182549012832008412165759636414336116974908889100762420792118787127270615324110361812252
def reachable : Nat := 6091501620533207900108234663783834705084240630856191762332470184524581481060714968389708538530489091573056949297385288432961764024819299331109538644271843
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
theorem oddSide_length : oddSide.length = 49 := by decide
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

end Snake9.Regrowth.E112249
