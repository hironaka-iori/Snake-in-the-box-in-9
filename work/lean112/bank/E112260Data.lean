import RegrowthParityCounts
namespace Snake9.Regrowth.E112260
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 4, 36, 164, 180, 176, 48, 50, 18, 22, 150, 134, 142, 14, 10, 42, 170, 186, 190, 62, 60, 28, 24, 152, 136, 137, 9, 13, 45, 47, 175, 167, 183, 55, 53, 21, 149, 157, 189, 185, 57, 59, 27, 155, 147, 131, 3, 35, 33, 161, 417, 425, 297, 299, 267, 271, 399, 391, 407, 279, 275, 307, 435, 443, 447, 319, 317, 285, 281, 409, 401, 400, 272, 276, 308, 310, 438, 422, 430, 302, 300, 268, 396, 412, 444, 440, 312, 314, 282, 410, 394, 386, 258, 290, 288, 352, 368, 496, 497, 505, 377, 379, 347, 351, 479, 478, 510, 382, 380, 348, 344, 328]
def region : List Vertex := [(65 : Vertex), (66 : Vertex), (69 : Vertex), (70 : Vertex), (71 : Vertex), (72 : Vertex), (75 : Vertex), (76 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (83 : Vertex), (84 : Vertex), (87 : Vertex), (89 : Vertex), (90 : Vertex), (93 : Vertex), (94 : Vertex), (98 : Vertex), (101 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (107 : Vertex), (108 : Vertex), (110 : Vertex), (113 : Vertex), (115 : Vertex), (116 : Vertex), (118 : Vertex), (120 : Vertex), (122 : Vertex), (125 : Vertex), (127 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (196 : Vertex), (197 : Vertex), (199 : Vertex), (202 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (220 : Vertex), (224 : Vertex), (226 : Vertex), (227 : Vertex), (229 : Vertex), (230 : Vertex), (232 : Vertex), (233 : Vertex), (235 : Vertex), (236 : Vertex), (237 : Vertex), (238 : Vertex), (242 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (248 : Vertex), (251 : Vertex), (252 : Vertex), (255 : Vertex), (257 : Vertex), (261 : Vertex), (293 : Vertex), (295 : Vertex), (321 : Vertex), (323 : Vertex), (324 : Vertex), (325 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (330 : Vertex), (333 : Vertex), (334 : Vertex), (337 : Vertex), (338 : Vertex), (341 : Vertex), (342 : Vertex), (355 : Vertex), (357 : Vertex), (358 : Vertex), (359 : Vertex), (362 : Vertex), (365 : Vertex), (367 : Vertex), (373 : Vertex), (375 : Vertex), (448 : Vertex), (449 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (456 : Vertex), (457 : Vertex), (459 : Vertex), (461 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (469 : Vertex), (482 : Vertex), (483 : Vertex), (484 : Vertex), (485 : Vertex), (487 : Vertex), (488 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (495 : Vertex), (503 : Vertex)]
def oddSide : List Vertex := [(69 : Vertex), (70 : Vertex), (76 : Vertex), (79 : Vertex), (81 : Vertex), (84 : Vertex), (87 : Vertex), (93 : Vertex), (94 : Vertex), (98 : Vertex), (103 : Vertex), (104 : Vertex), (107 : Vertex), (110 : Vertex), (115 : Vertex), (118 : Vertex), (122 : Vertex), (127 : Vertex), (193 : Vertex), (194 : Vertex), (196 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex), (208 : Vertex), (217 : Vertex), (218 : Vertex), (220 : Vertex), (224 : Vertex), (227 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (236 : Vertex), (242 : Vertex), (248 : Vertex), (251 : Vertex), (261 : Vertex), (295 : Vertex), (321 : Vertex), (324 : Vertex), (327 : Vertex), (328 : Vertex), (333 : Vertex), (334 : Vertex), (341 : Vertex), (342 : Vertex), (355 : Vertex), (357 : Vertex), (358 : Vertex), (362 : Vertex), (367 : Vertex), (375 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (454 : Vertex), (457 : Vertex), (466 : Vertex), (468 : Vertex), (482 : Vertex), (484 : Vertex), (487 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex)]
def evenSide : List Vertex := [(65 : Vertex), (66 : Vertex), (71 : Vertex), (72 : Vertex), (75 : Vertex), (80 : Vertex), (83 : Vertex), (89 : Vertex), (90 : Vertex), (101 : Vertex), (102 : Vertex), (105 : Vertex), (108 : Vertex), (113 : Vertex), (116 : Vertex), (120 : Vertex), (125 : Vertex), (192 : Vertex), (197 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex), (215 : Vertex), (226 : Vertex), (232 : Vertex), (235 : Vertex), (237 : Vertex), (238 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (252 : Vertex), (255 : Vertex), (257 : Vertex), (293 : Vertex), (323 : Vertex), (325 : Vertex), (326 : Vertex), (329 : Vertex), (330 : Vertex), (337 : Vertex), (338 : Vertex), (359 : Vertex), (365 : Vertex), (373 : Vertex), (449 : Vertex), (452 : Vertex), (456 : Vertex), (459 : Vertex), (461 : Vertex), (467 : Vertex), (469 : Vertex), (483 : Vertex), (485 : Vertex), (490 : Vertex), (492 : Vertex), (495 : Vertex), (503 : Vertex)]
def others : List Vertex := [(65 : Vertex), (66 : Vertex), (69 : Vertex), (70 : Vertex), (71 : Vertex), (72 : Vertex), (75 : Vertex), (76 : Vertex), (79 : Vertex), (80 : Vertex), (81 : Vertex), (83 : Vertex), (84 : Vertex), (87 : Vertex), (89 : Vertex), (90 : Vertex), (93 : Vertex), (94 : Vertex), (98 : Vertex), (101 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (107 : Vertex), (108 : Vertex), (110 : Vertex), (113 : Vertex), (115 : Vertex), (116 : Vertex), (118 : Vertex), (120 : Vertex), (122 : Vertex), (125 : Vertex), (127 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (196 : Vertex), (197 : Vertex), (199 : Vertex), (202 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (220 : Vertex), (224 : Vertex), (226 : Vertex), (227 : Vertex), (229 : Vertex), (230 : Vertex), (232 : Vertex), (233 : Vertex), (235 : Vertex), (236 : Vertex), (237 : Vertex), (238 : Vertex), (242 : Vertex), (243 : Vertex), (245 : Vertex), (246 : Vertex), (248 : Vertex), (251 : Vertex), (252 : Vertex), (255 : Vertex), (257 : Vertex), (261 : Vertex), (293 : Vertex), (295 : Vertex), (321 : Vertex), (323 : Vertex), (324 : Vertex), (325 : Vertex), (326 : Vertex), (327 : Vertex), (329 : Vertex), (330 : Vertex), (333 : Vertex), (334 : Vertex), (337 : Vertex), (338 : Vertex), (341 : Vertex), (342 : Vertex), (355 : Vertex), (357 : Vertex), (358 : Vertex), (359 : Vertex), (362 : Vertex), (365 : Vertex), (367 : Vertex), (373 : Vertex), (375 : Vertex), (448 : Vertex), (449 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (456 : Vertex), (457 : Vertex), (459 : Vertex), (461 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (469 : Vertex), (482 : Vertex), (483 : Vertex), (484 : Vertex), (485 : Vertex), (487 : Vertex), (488 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (495 : Vertex), (503 : Vertex)]
def head : Vertex := 328
def ban : Nat := 13381469175505975879638935563978691222657976745417662075482017948434908704697649073223263566737071840304228695646998945074910495962612549339344827945320447
def reachable : Nat := 26338754436621219934734532506307440519363038159160987527503631341207220854276082192292059902432467306054045815505775912846920774330960949894712368562176
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
theorem oddSide_length : oddSide.length = 66 := by decide
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

end Snake9.Regrowth.E112260
