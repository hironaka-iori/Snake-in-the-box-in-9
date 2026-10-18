import RegrowthParityCounts
namespace Snake9.Regrowth.E112188
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 17, 19, 18, 26, 30, 28, 29, 13, 15, 7, 6, 70, 102, 118, 126, 124, 125, 109, 105, 361, 377, 379, 378, 362, 366, 364, 356, 372, 373, 375, 359, 295, 303, 301, 317, 316, 318, 310, 306, 307, 305, 289, 288, 296, 424, 168, 160, 161, 177, 179, 178, 186, 190, 188, 189, 173, 175, 167, 166, 422, 420, 436, 437, 439, 447, 443, 427, 491, 495, 493, 485, 481, 497, 499, 498, 502, 510, 508, 504, 248, 249, 251, 255, 247, 245, 244, 228, 236, 238, 234, 226, 227, 99, 35, 34, 42, 46, 44, 36, 37, 53, 55, 63, 59, 57, 56, 48, 112, 80, 84]
def region : List Vertex := [(69 : Vertex), (72 : Vertex), (74 : Vertex), (75 : Vertex), (76 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (89 : Vertex), (91 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (197 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (203 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (323 : Vertex), (325 : Vertex), (328 : Vertex), (331 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (344 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (351 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (391 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (448 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(69 : Vertex), (74 : Vertex), (76 : Vertex), (84 : Vertex), (87 : Vertex), (91 : Vertex), (131 : Vertex), (133 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (155 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (203 : Vertex), (205 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (259 : Vertex), (261 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (276 : Vertex), (279 : Vertex), (280 : Vertex), (283 : Vertex), (321 : Vertex), (322 : Vertex), (328 : Vertex), (331 : Vertex), (333 : Vertex), (339 : Vertex), (342 : Vertex), (348 : Vertex), (351 : Vertex), (385 : Vertex), (386 : Vertex), (391 : Vertex), (397 : Vertex), (398 : Vertex), (400 : Vertex), (403 : Vertex), (406 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (448 : Vertex), (451 : Vertex), (454 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (468 : Vertex), (471 : Vertex), (475 : Vertex), (477 : Vertex)]
def evenSide : List Vertex := [(72 : Vertex), (75 : Vertex), (85 : Vertex), (89 : Vertex), (95 : Vertex), (130 : Vertex), (132 : Vertex), (139 : Vertex), (142 : Vertex), (144 : Vertex), (149 : Vertex), (150 : Vertex), (153 : Vertex), (159 : Vertex), (192 : Vertex), (197 : Vertex), (201 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (260 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (277 : Vertex), (281 : Vertex), (287 : Vertex), (320 : Vertex), (323 : Vertex), (325 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (344 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (387 : Vertex), (389 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (408 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (452 : Vertex), (455 : Vertex), (456 : Vertex), (462 : Vertex), (464 : Vertex), (469 : Vertex), (473 : Vertex), (474 : Vertex), (479 : Vertex)]
def others : List Vertex := [(69 : Vertex), (72 : Vertex), (74 : Vertex), (75 : Vertex), (76 : Vertex), (85 : Vertex), (87 : Vertex), (89 : Vertex), (91 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (197 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (203 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (323 : Vertex), (325 : Vertex), (328 : Vertex), (331 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (344 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (351 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (391 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (448 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex), (479 : Vertex)]
def head : Vertex := 84
def ban : Nat := 13407807927812336046831226117181315322253357071763715077760619604805245773099803078658070488638408779935494326474505588981691511919939391666528720238149631
def reachable : Nat := 2130261052742798881024530805226008748828678299962941838916518256973743898143803809528494647754537531711980461872062370892007178279904928767934464
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

end Snake9.Regrowth.E112188
