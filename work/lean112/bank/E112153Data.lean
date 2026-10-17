import RegrowthParityCounts
namespace Snake9.Regrowth.E112153
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[19, 17, 25, 9, 41, 105, 104, 96, 98, 114, 115, 113, 117, 125, 124, 126, 110, 111, 103, 39, 167, 175, 174, 190, 188, 189, 185, 177, 179, 178, 162, 160, 168, 424, 440, 442, 443, 427, 419, 417, 421, 437, 436, 438, 422, 486, 482, 498, 499, 497, 505, 509, 511, 255, 247, 246, 244, 240, 248, 250, 234, 235, 227, 225, 229, 237, 236, 492, 364, 365, 357, 353, 355, 363, 379, 378, 376, 368, 372, 374, 375, 311, 307, 305, 313, 317, 316, 318, 302, 298, 290, 288, 292, 36, 52, 48, 56, 58, 59, 63, 31, 95, 87, 86, 84, 80, 88, 90, 74, 75, 67, 65]
def region : List Vertex := [(0 : Vertex), (2 : Vertex), (5 : Vertex), (6 : Vertex), (12 : Vertex), (14 : Vertex), (28 : Vertex), (65 : Vertex), (69 : Vertex), (76 : Vertex), (77 : Vertex), (129 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (154 : Vertex), (155 : Vertex), (192 : Vertex), (194 : Vertex), (196 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (206 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (213 : Vertex), (217 : Vertex), (219 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (257 : Vertex), (259 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (268 : Vertex), (269 : Vertex), (271 : Vertex), (272 : Vertex), (274 : Vertex), (276 : Vertex), (277 : Vertex), (278 : Vertex), (280 : Vertex), (282 : Vertex), (283 : Vertex), (320 : Vertex), (322 : Vertex), (324 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (334 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (341 : Vertex), (345 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (391 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (407 : Vertex), (409 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (415 : Vertex), (448 : Vertex), (449 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (471 : Vertex), (472 : Vertex), (474 : Vertex), (475 : Vertex), (476 : Vertex), (478 : Vertex)]
def oddSide : List Vertex := [(2 : Vertex), (14 : Vertex), (28 : Vertex), (69 : Vertex), (76 : Vertex), (131 : Vertex), (133 : Vertex), (134 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (155 : Vertex), (194 : Vertex), (196 : Vertex), (199 : Vertex), (200 : Vertex), (206 : Vertex), (211 : Vertex), (213 : Vertex), (217 : Vertex), (220 : Vertex), (259 : Vertex), (261 : Vertex), (262 : Vertex), (268 : Vertex), (271 : Vertex), (274 : Vertex), (276 : Vertex), (280 : Vertex), (283 : Vertex), (322 : Vertex), (324 : Vertex), (327 : Vertex), (328 : Vertex), (334 : Vertex), (339 : Vertex), (341 : Vertex), (345 : Vertex), (348 : Vertex), (386 : Vertex), (388 : Vertex), (391 : Vertex), (397 : Vertex), (398 : Vertex), (400 : Vertex), (403 : Vertex), (409 : Vertex), (412 : Vertex), (415 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (463 : Vertex), (468 : Vertex), (471 : Vertex), (472 : Vertex), (475 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (5 : Vertex), (6 : Vertex), (12 : Vertex), (65 : Vertex), (77 : Vertex), (129 : Vertex), (132 : Vertex), (139 : Vertex), (141 : Vertex), (144 : Vertex), (149 : Vertex), (150 : Vertex), (154 : Vertex), (192 : Vertex), (198 : Vertex), (201 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (219 : Vertex), (221 : Vertex), (222 : Vertex), (257 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (269 : Vertex), (272 : Vertex), (277 : Vertex), (278 : Vertex), (282 : Vertex), (320 : Vertex), (326 : Vertex), (329 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (407 : Vertex), (413 : Vertex), (414 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex), (456 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex), (464 : Vertex), (469 : Vertex), (470 : Vertex), (474 : Vertex), (476 : Vertex)]
def others : List Vertex := [(0 : Vertex), (2 : Vertex), (5 : Vertex), (6 : Vertex), (12 : Vertex), (14 : Vertex), (28 : Vertex), (69 : Vertex), (76 : Vertex), (77 : Vertex), (129 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (154 : Vertex), (155 : Vertex), (192 : Vertex), (194 : Vertex), (196 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (206 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (213 : Vertex), (217 : Vertex), (219 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (257 : Vertex), (259 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (268 : Vertex), (269 : Vertex), (271 : Vertex), (272 : Vertex), (274 : Vertex), (276 : Vertex), (277 : Vertex), (278 : Vertex), (280 : Vertex), (282 : Vertex), (283 : Vertex), (320 : Vertex), (322 : Vertex), (324 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (334 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (341 : Vertex), (345 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (391 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (407 : Vertex), (409 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (415 : Vertex), (448 : Vertex), (449 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (471 : Vertex), (472 : Vertex), (474 : Vertex), (475 : Vertex), (476 : Vertex), (478 : Vertex)]
def head : Vertex := 65
def ban : Nat := 13407807928796999958475054408292274305957932160671226766633793177222670951744285878207736178411886947219018774510665603996825981921448771597494803618574234
def reachable : Nat := 1145597141098970589913571821521433659921166611089768266499093078329261098594138119755016480471013083675820446856927900890497798348938845387509861
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
theorem oddSide_length : oddSide.length = 62 := by decide
theorem evenSide_length : evenSide.length = 62 := by decide

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

end Snake9.Regrowth.E112153
