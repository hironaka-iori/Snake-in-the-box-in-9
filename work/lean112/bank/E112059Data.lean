import RegrowthParityCounts
namespace Snake9.Regrowth.E112059
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[140, 136, 392, 384, 385, 401, 403, 402, 410, 414, 412, 413, 397, 399, 391, 390, 134, 166, 182, 190, 188, 189, 173, 169, 233, 249, 251, 250, 234, 238, 236, 228, 244, 245, 247, 231, 487, 495, 493, 509, 508, 510, 502, 498, 499, 497, 481, 480, 488, 360, 296, 288, 289, 305, 307, 306, 314, 318, 316, 317, 301, 303, 295, 294, 358, 356, 372, 373, 375, 383, 379, 363, 107, 111, 109, 101, 97, 113, 115, 114, 118, 126, 124, 120, 56, 57, 59, 63, 55, 53, 52, 36, 44, 46, 42, 34, 35, 163, 419, 418, 426, 430, 428, 420, 421, 437, 439, 447, 443, 441, 440, 432]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (5 : Vertex), (7 : Vertex), (9 : Vertex), (11 : Vertex), (13 : Vertex), (15 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (64 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (70 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (74 : Vertex), (76 : Vertex), (78 : Vertex), (80 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (89 : Vertex), (90 : Vertex), (91 : Vertex), (93 : Vertex), (95 : Vertex), (133 : Vertex), (139 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (155 : Vertex), (159 : Vertex), (160 : Vertex), (176 : Vertex), (177 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (203 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (216 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (223 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (278 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (323 : Vertex), (325 : Vertex), (327 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex), (333 : Vertex), (334 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (344 : Vertex), (345 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (432 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (11 : Vertex), (13 : Vertex), (16 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (64 : Vertex), (67 : Vertex), (70 : Vertex), (73 : Vertex), (74 : Vertex), (76 : Vertex), (84 : Vertex), (87 : Vertex), (91 : Vertex), (93 : Vertex), (133 : Vertex), (148 : Vertex), (151 : Vertex), (155 : Vertex), (176 : Vertex), (193 : Vertex), (194 : Vertex), (203 : Vertex), (205 : Vertex), (208 : Vertex), (211 : Vertex), (214 : Vertex), (220 : Vertex), (223 : Vertex), (259 : Vertex), (261 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (276 : Vertex), (279 : Vertex), (280 : Vertex), (283 : Vertex), (321 : Vertex), (322 : Vertex), (327 : Vertex), (333 : Vertex), (334 : Vertex), (336 : Vertex), (339 : Vertex), (342 : Vertex), (345 : Vertex), (346 : Vertex), (348 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (468 : Vertex), (471 : Vertex), (472 : Vertex), (475 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (5 : Vertex), (9 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (68 : Vertex), (71 : Vertex), (72 : Vertex), (78 : Vertex), (80 : Vertex), (85 : Vertex), (89 : Vertex), (90 : Vertex), (95 : Vertex), (139 : Vertex), (144 : Vertex), (149 : Vertex), (153 : Vertex), (159 : Vertex), (160 : Vertex), (177 : Vertex), (192 : Vertex), (195 : Vertex), (197 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (216 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (260 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (277 : Vertex), (278 : Vertex), (281 : Vertex), (287 : Vertex), (320 : Vertex), (323 : Vertex), (325 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (344 : Vertex), (349 : Vertex), (350 : Vertex), (432 : Vertex), (450 : Vertex), (452 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (469 : Vertex), (473 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (5 : Vertex), (7 : Vertex), (9 : Vertex), (11 : Vertex), (13 : Vertex), (15 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (64 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (70 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (74 : Vertex), (76 : Vertex), (78 : Vertex), (80 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (89 : Vertex), (90 : Vertex), (91 : Vertex), (93 : Vertex), (95 : Vertex), (133 : Vertex), (139 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (155 : Vertex), (159 : Vertex), (160 : Vertex), (176 : Vertex), (177 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (203 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (216 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (223 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (278 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (322 : Vertex), (323 : Vertex), (325 : Vertex), (327 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex), (333 : Vertex), (334 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (344 : Vertex), (345 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex)]
def head : Vertex := 432
def ban : Nat := 13407807928239136420970781354009551728869512619858374972567888099203410875291140511234896984274054984745848316043581815920503528132394832393072991555048796
def reachable : Nat := 1703460678603243644196294398609853200734018405155673344518353154782406465566977313892848442944183542142904234933250354679551737553360657451035299
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
theorem evenSide_length : evenSide.length = 64 := by decide

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

end Snake9.Regrowth.E112059
