import RegrowthParityCounts
namespace Snake9.Regrowth.E112099
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[73, 72, 74, 78, 70, 68, 84, 85, 93, 95, 91, 83, 82, 18, 146, 147, 155, 159, 157, 149, 133, 132, 134, 142, 138, 136, 137, 393, 397, 399, 391, 387, 386, 384, 400, 404, 412, 414, 410, 474, 458, 462, 454, 452, 453, 449, 481, 225, 233, 232, 234, 238, 230, 228, 244, 245, 253, 255, 251, 243, 242, 498, 370, 371, 379, 383, 381, 373, 357, 356, 358, 366, 362, 360, 361, 297, 301, 303, 295, 291, 290, 288, 304, 308, 316, 318, 314, 58, 42, 46, 38, 36, 37, 53, 55, 119, 118, 126, 124, 108, 109, 111, 107, 99, 98, 96, 112, 113, 121, 57, 185, 177]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (7 : Vertex), (11 : Vertex), (12 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (24 : Vertex), (28 : Vertex), (30 : Vertex), (160 : Vertex), (162 : Vertex), (163 : Vertex), (167 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (182 : Vertex), (188 : Vertex), (190 : Vertex), (192 : Vertex), (194 : Vertex), (195 : Vertex), (199 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (214 : Vertex), (215 : Vertex), (216 : Vertex), (217 : Vertex), (220 : Vertex), (222 : Vertex), (257 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (264 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (270 : Vertex), (273 : Vertex), (275 : Vertex), (277 : Vertex), (278 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (283 : Vertex), (285 : Vertex), (287 : Vertex), (320 : Vertex), (322 : Vertex), (323 : Vertex), (327 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (348 : Vertex), (350 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (424 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (430 : Vertex), (433 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (439 : Vertex), (440 : Vertex), (443 : Vertex), (445 : Vertex), (447 : Vertex), (467 : Vertex), (471 : Vertex), (473 : Vertex), (477 : Vertex), (479 : Vertex), (487 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (495 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (508 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (11 : Vertex), (13 : Vertex), (28 : Vertex), (162 : Vertex), (167 : Vertex), (171 : Vertex), (173 : Vertex), (176 : Vertex), (182 : Vertex), (188 : Vertex), (194 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex), (208 : Vertex), (214 : Vertex), (217 : Vertex), (220 : Vertex), (261 : Vertex), (262 : Vertex), (266 : Vertex), (268 : Vertex), (273 : Vertex), (279 : Vertex), (280 : Vertex), (283 : Vertex), (285 : Vertex), (322 : Vertex), (327 : Vertex), (331 : Vertex), (333 : Vertex), (336 : Vertex), (342 : Vertex), (345 : Vertex), (348 : Vertex), (421 : Vertex), (422 : Vertex), (426 : Vertex), (428 : Vertex), (433 : Vertex), (439 : Vertex), (440 : Vertex), (443 : Vertex), (445 : Vertex), (471 : Vertex), (477 : Vertex), (487 : Vertex), (491 : Vertex), (493 : Vertex), (505 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (12 : Vertex), (15 : Vertex), (17 : Vertex), (24 : Vertex), (30 : Vertex), (160 : Vertex), (163 : Vertex), (172 : Vertex), (175 : Vertex), (177 : Vertex), (190 : Vertex), (192 : Vertex), (195 : Vertex), (204 : Vertex), (207 : Vertex), (209 : Vertex), (215 : Vertex), (216 : Vertex), (222 : Vertex), (257 : Vertex), (260 : Vertex), (264 : Vertex), (267 : Vertex), (270 : Vertex), (275 : Vertex), (277 : Vertex), (278 : Vertex), (281 : Vertex), (287 : Vertex), (320 : Vertex), (323 : Vertex), (332 : Vertex), (335 : Vertex), (337 : Vertex), (343 : Vertex), (344 : Vertex), (350 : Vertex), (420 : Vertex), (424 : Vertex), (427 : Vertex), (430 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (447 : Vertex), (467 : Vertex), (473 : Vertex), (479 : Vertex), (492 : Vertex), (495 : Vertex), (503 : Vertex), (504 : Vertex), (510 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (7 : Vertex), (11 : Vertex), (12 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (24 : Vertex), (28 : Vertex), (30 : Vertex), (160 : Vertex), (162 : Vertex), (163 : Vertex), (167 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (182 : Vertex), (188 : Vertex), (190 : Vertex), (192 : Vertex), (194 : Vertex), (195 : Vertex), (199 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (214 : Vertex), (215 : Vertex), (216 : Vertex), (217 : Vertex), (220 : Vertex), (222 : Vertex), (257 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (264 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (270 : Vertex), (273 : Vertex), (275 : Vertex), (277 : Vertex), (278 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (283 : Vertex), (285 : Vertex), (287 : Vertex), (320 : Vertex), (322 : Vertex), (323 : Vertex), (327 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (348 : Vertex), (350 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (424 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (430 : Vertex), (433 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (439 : Vertex), (440 : Vertex), (443 : Vertex), (445 : Vertex), (447 : Vertex), (467 : Vertex), (471 : Vertex), (473 : Vertex), (477 : Vertex), (479 : Vertex), (487 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (495 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (508 : Vertex), (510 : Vertex)]
def head : Vertex := 177
def ban : Nat := 9034410629383863293353646302841384740827593017609775028848409887734940763352769874141646448980864142716462515237729023287449727117541215300498060987942772
def reachable : Nat := 4373397300558733806220378695364461386651772802982618348875151555986823266720777102660227849186039284973569342948757027566304155694405354645935588018141323
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
theorem oddSide_length : oddSide.length = 53 := by decide
theorem evenSide_length : evenSide.length = 55 := by decide

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

end Snake9.Regrowth.E112099
