import RegrowthParityCounts
namespace Snake9.Regrowth.E112023
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[376, 377, 379, 383, 375, 373, 357, 356, 364, 366, 362, 354, 355, 483, 419, 418, 426, 430, 428, 420, 421, 437, 439, 447, 443, 441, 440, 432, 496, 498, 502, 510, 508, 509, 493, 489, 233, 249, 251, 250, 234, 238, 236, 228, 244, 245, 247, 231, 167, 175, 173, 189, 188, 190, 182, 178, 179, 177, 161, 160, 168, 40, 104, 96, 97, 113, 115, 114, 118, 126, 124, 125, 109, 111, 107, 43, 59, 63, 55, 53, 52, 308, 316, 318, 314, 306, 307, 305, 289, 297, 301, 303, 295, 294, 38, 6, 22, 30, 28, 29, 13, 9, 73, 89, 91, 90, 74, 78, 76, 68, 84, 85]
def region : List Vertex := [(0 : Vertex), (3 : Vertex), (16 : Vertex), (17 : Vertex), (19 : Vertex), (67 : Vertex), (71 : Vertex), (85 : Vertex), (87 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (198 : Vertex), (200 : Vertex), (203 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (216 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (223 : Vertex), (256 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (264 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (331 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (385 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (395 : Vertex), (397 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (404 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (448 : Vertex), (449 : Vertex), (450 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (458 : Vertex), (459 : Vertex), (460 : Vertex), (462 : Vertex), (463 : Vertex), (465 : Vertex), (467 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(16 : Vertex), (19 : Vertex), (67 : Vertex), (87 : Vertex), (131 : Vertex), (133 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (155 : Vertex), (193 : Vertex), (194 : Vertex), (200 : Vertex), (203 : Vertex), (205 : Vertex), (208 : Vertex), (211 : Vertex), (214 : Vertex), (220 : Vertex), (223 : Vertex), (256 : Vertex), (259 : Vertex), (261 : Vertex), (266 : Vertex), (268 : Vertex), (279 : Vertex), (280 : Vertex), (283 : Vertex), (321 : Vertex), (327 : Vertex), (328 : Vertex), (331 : Vertex), (333 : Vertex), (336 : Vertex), (339 : Vertex), (342 : Vertex), (348 : Vertex), (385 : Vertex), (391 : Vertex), (392 : Vertex), (395 : Vertex), (397 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (448 : Vertex), (453 : Vertex), (454 : Vertex), (458 : Vertex), (460 : Vertex), (463 : Vertex), (465 : Vertex), (468 : Vertex), (471 : Vertex), (472 : Vertex), (475 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (17 : Vertex), (71 : Vertex), (85 : Vertex), (130 : Vertex), (132 : Vertex), (139 : Vertex), (142 : Vertex), (144 : Vertex), (149 : Vertex), (153 : Vertex), (154 : Vertex), (159 : Vertex), (192 : Vertex), (195 : Vertex), (197 : Vertex), (198 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (216 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (260 : Vertex), (264 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (277 : Vertex), (281 : Vertex), (287 : Vertex), (320 : Vertex), (326 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (390 : Vertex), (393 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (404 : Vertex), (413 : Vertex), (414 : Vertex), (449 : Vertex), (450 : Vertex), (452 : Vertex), (455 : Vertex), (456 : Vertex), (459 : Vertex), (462 : Vertex), (467 : Vertex), (469 : Vertex), (473 : Vertex), (474 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (3 : Vertex), (16 : Vertex), (17 : Vertex), (19 : Vertex), (67 : Vertex), (71 : Vertex), (87 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (198 : Vertex), (200 : Vertex), (203 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (216 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (223 : Vertex), (256 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (264 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (331 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (385 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (395 : Vertex), (397 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (404 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (448 : Vertex), (449 : Vertex), (450 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (458 : Vertex), (459 : Vertex), (460 : Vertex), (462 : Vertex), (463 : Vertex), (465 : Vertex), (467 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (479 : Vertex)]
def head : Vertex := 85
def ban : Nat := 13407807928189906626048929301228961879035313063537069312925307431945415758115878425566723308273492786959513551914676568977581209357754290636585666627305462
def reachable : Nat := 1752690473525095696976884248444052757055324064798254011776348271957668551235150989893410640730518306271809481876172673454192279309847982378778633
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
theorem oddSide_length : oddSide.length = 59 := by decide
theorem evenSide_length : evenSide.length = 61 := by decide

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

end Snake9.Regrowth.E112023
