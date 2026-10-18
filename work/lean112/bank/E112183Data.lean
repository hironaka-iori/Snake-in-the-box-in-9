import RegrowthParityCounts
namespace Snake9.Regrowth.E112183
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[268, 264, 392, 384, 385, 401, 403, 402, 406, 414, 412, 413, 397, 399, 391, 135, 151, 149, 148, 132, 140, 142, 138, 154, 155, 153, 137, 201, 205, 221, 220, 222, 214, 198, 230, 486, 487, 495, 493, 509, 508, 510, 506, 498, 499, 497, 481, 480, 488, 232, 104, 96, 97, 113, 115, 114, 118, 126, 124, 125, 109, 111, 103, 39, 55, 53, 52, 36, 44, 46, 42, 58, 59, 57, 41, 297, 301, 317, 316, 318, 310, 306, 304, 368, 376, 377, 379, 383, 375, 373, 357, 356, 364, 366, 362, 354, 355, 291, 419, 418, 426, 430, 428, 420, 436, 437, 439, 447, 443, 441, 440, 184]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (2 : Vertex), (3 : Vertex), (5 : Vertex), (6 : Vertex), (11 : Vertex), (13 : Vertex), (15 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (24 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (31 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (74 : Vertex), (75 : Vertex), (76 : Vertex), (78 : Vertex), (80 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (90 : Vertex), (91 : Vertex), (95 : Vertex), (160 : Vertex), (161 : Vertex), (165 : Vertex), (171 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (184 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (192 : Vertex), (195 : Vertex), (208 : Vertex), (209 : Vertex), (211 : Vertex), (227 : Vertex), (229 : Vertex), (235 : Vertex), (240 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (249 : Vertex), (251 : Vertex), (255 : Vertex), (258 : Vertex), (261 : Vertex), (262 : Vertex), (267 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (329 : Vertex), (331 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (340 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (458 : Vertex), (459 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (2 : Vertex), (11 : Vertex), (13 : Vertex), (16 : Vertex), (19 : Vertex), (22 : Vertex), (28 : Vertex), (31 : Vertex), (67 : Vertex), (69 : Vertex), (74 : Vertex), (76 : Vertex), (84 : Vertex), (87 : Vertex), (88 : Vertex), (91 : Vertex), (161 : Vertex), (171 : Vertex), (173 : Vertex), (176 : Vertex), (179 : Vertex), (182 : Vertex), (188 : Vertex), (208 : Vertex), (211 : Vertex), (227 : Vertex), (229 : Vertex), (244 : Vertex), (247 : Vertex), (251 : Vertex), (261 : Vertex), (262 : Vertex), (276 : Vertex), (279 : Vertex), (283 : Vertex), (321 : Vertex), (327 : Vertex), (331 : Vertex), (333 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (451 : Vertex), (453 : Vertex), (458 : Vertex), (460 : Vertex), (468 : Vertex), (471 : Vertex), (472 : Vertex), (475 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (5 : Vertex), (6 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (24 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (68 : Vertex), (75 : Vertex), (78 : Vertex), (80 : Vertex), (85 : Vertex), (89 : Vertex), (90 : Vertex), (95 : Vertex), (160 : Vertex), (165 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (184 : Vertex), (189 : Vertex), (190 : Vertex), (192 : Vertex), (195 : Vertex), (209 : Vertex), (235 : Vertex), (240 : Vertex), (245 : Vertex), (249 : Vertex), (255 : Vertex), (258 : Vertex), (267 : Vertex), (277 : Vertex), (281 : Vertex), (282 : Vertex), (287 : Vertex), (320 : Vertex), (326 : Vertex), (329 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (340 : Vertex), (349 : Vertex), (350 : Vertex), (450 : Vertex), (452 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (469 : Vertex), (473 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (2 : Vertex), (3 : Vertex), (5 : Vertex), (6 : Vertex), (11 : Vertex), (13 : Vertex), (15 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (24 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (31 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (74 : Vertex), (75 : Vertex), (76 : Vertex), (78 : Vertex), (80 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (90 : Vertex), (91 : Vertex), (95 : Vertex), (160 : Vertex), (161 : Vertex), (165 : Vertex), (171 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (182 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (192 : Vertex), (195 : Vertex), (208 : Vertex), (209 : Vertex), (211 : Vertex), (227 : Vertex), (229 : Vertex), (235 : Vertex), (240 : Vertex), (244 : Vertex), (245 : Vertex), (247 : Vertex), (249 : Vertex), (251 : Vertex), (255 : Vertex), (258 : Vertex), (261 : Vertex), (262 : Vertex), (267 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (281 : Vertex), (282 : Vertex), (283 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (329 : Vertex), (331 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (340 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (458 : Vertex), (459 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex)]
def head : Vertex := 184
def ban : Nat := 13407807928239136793112208193360279690123302258516802011134237544179720128264774585862234446409909278977263832099332584080226082377151210887227854885509008
def reachable : Nat := 1703460306461816804845566437356063562075591366589323899542043901808772390939639851756994148712768026087153466773527800434795359059205794120575087
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
theorem oddSide_length : oddSide.length = 52 := by decide
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

end Snake9.Regrowth.E112183
