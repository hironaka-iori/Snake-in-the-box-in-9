import RegrowthParityCounts
namespace Snake9.Regrowth.E112109
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[88, 89, 91, 95, 87, 85, 69, 68, 76, 78, 74, 66, 67, 3, 131, 130, 138, 142, 140, 132, 148, 149, 151, 159, 155, 153, 152, 408, 412, 414, 406, 402, 403, 401, 385, 389, 397, 399, 395, 459, 475, 479, 471, 469, 468, 464, 496, 240, 248, 249, 251, 255, 247, 245, 229, 228, 236, 238, 234, 226, 227, 483, 355, 354, 362, 366, 364, 356, 372, 373, 375, 383, 379, 377, 376, 312, 316, 318, 310, 306, 307, 305, 289, 293, 301, 303, 299, 43, 59, 63, 55, 53, 52, 36, 38, 102, 103, 111, 109, 125, 124, 126, 122, 114, 115, 113, 97, 96, 104, 40, 168, 160]
def region : List Vertex := [(0 : Vertex), (9 : Vertex), (13 : Vertex), (15 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (160 : Vertex), (161 : Vertex), (167 : Vertex), (173 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (256 : Vertex), (258 : Vertex), (260 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (285 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (416 : Vertex), (418 : Vertex), (420 : Vertex), (422 : Vertex), (423 : Vertex), (425 : Vertex), (426 : Vertex), (428 : Vertex), (430 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (445 : Vertex), (447 : Vertex), (450 : Vertex), (454 : Vertex), (456 : Vertex), (460 : Vertex), (462 : Vertex), (486 : Vertex), (488 : Vertex), (489 : Vertex), (493 : Vertex), (495 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(13 : Vertex), (16 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (161 : Vertex), (167 : Vertex), (173 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (256 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (276 : Vertex), (279 : Vertex), (283 : Vertex), (285 : Vertex), (321 : Vertex), (327 : Vertex), (328 : Vertex), (333 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (416 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (428 : Vertex), (436 : Vertex), (439 : Vertex), (443 : Vertex), (445 : Vertex), (454 : Vertex), (460 : Vertex), (488 : Vertex), (493 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (9 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (29 : Vertex), (30 : Vertex), (160 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (189 : Vertex), (190 : Vertex), (192 : Vertex), (198 : Vertex), (201 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (260 : Vertex), (263 : Vertex), (264 : Vertex), (270 : Vertex), (272 : Vertex), (277 : Vertex), (281 : Vertex), (282 : Vertex), (287 : Vertex), (320 : Vertex), (326 : Vertex), (329 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (349 : Vertex), (350 : Vertex), (418 : Vertex), (420 : Vertex), (423 : Vertex), (430 : Vertex), (437 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex), (450 : Vertex), (456 : Vertex), (462 : Vertex), (486 : Vertex), (489 : Vertex), (495 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(0 : Vertex), (9 : Vertex), (13 : Vertex), (15 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (161 : Vertex), (167 : Vertex), (173 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (256 : Vertex), (258 : Vertex), (260 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (285 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (416 : Vertex), (418 : Vertex), (420 : Vertex), (422 : Vertex), (423 : Vertex), (425 : Vertex), (426 : Vertex), (428 : Vertex), (430 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (441 : Vertex), (442 : Vertex), (443 : Vertex), (445 : Vertex), (447 : Vertex), (450 : Vertex), (454 : Vertex), (456 : Vertex), (460 : Vertex), (462 : Vertex), (486 : Vertex), (488 : Vertex), (489 : Vertex), (493 : Vertex), (495 : Vertex), (502 : Vertex), (506 : Vertex), (508 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 160
def ban : Nat := 7319170935140343293753359099884040497096632576084601275560974809368601916392101236891756281307045595649481384629757183891312676494524498712501002123632126
def reachable : Nat := 6088636994802253805820665898321805630382733244507792102162586634353162113681445739910118016859857832040550473556728866962441206317422071233932646882451969
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

end Snake9.Regrowth.E112109
