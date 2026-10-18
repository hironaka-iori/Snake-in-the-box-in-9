import RegrowthParityCounts
namespace Snake9.Regrowth.E112217
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[391, 399, 397, 413, 412, 414, 410, 402, 403, 401, 385, 384, 392, 456, 328, 320, 321, 337, 339, 338, 346, 350, 348, 349, 333, 335, 327, 326, 454, 486, 502, 510, 508, 509, 493, 489, 233, 249, 251, 250, 234, 238, 236, 228, 244, 245, 247, 231, 167, 175, 173, 189, 188, 190, 182, 178, 179, 177, 161, 160, 168, 40, 296, 288, 289, 305, 307, 306, 314, 318, 316, 317, 301, 303, 295, 294, 38, 36, 52, 53, 55, 63, 59, 43, 107, 111, 109, 101, 97, 113, 115, 114, 118, 126, 124, 120, 376, 377, 379, 383, 375, 373, 372, 356, 364, 366, 362, 354, 355, 483, 419, 418]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (2 : Vertex), (3 : Vertex), (5 : Vertex), (7 : Vertex), (9 : Vertex), (10 : Vertex), (12 : Vertex), (13 : Vertex), (14 : Vertex), (15 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (24 : Vertex), (25 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (73 : Vertex), (74 : Vertex), (76 : Vertex), (78 : Vertex), (80 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (89 : Vertex), (91 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (203 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (216 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (223 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (278 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (426 : Vertex), (428 : Vertex), (430 : Vertex), (432 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (443 : Vertex), (447 : Vertex), (453 : Vertex), (459 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex), (480 : Vertex), (496 : Vertex), (497 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (2 : Vertex), (7 : Vertex), (13 : Vertex), (14 : Vertex), (16 : Vertex), (19 : Vertex), (22 : Vertex), (25 : Vertex), (26 : Vertex), (28 : Vertex), (67 : Vertex), (73 : Vertex), (74 : Vertex), (76 : Vertex), (84 : Vertex), (87 : Vertex), (91 : Vertex), (131 : Vertex), (133 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (155 : Vertex), (193 : Vertex), (194 : Vertex), (203 : Vertex), (205 : Vertex), (208 : Vertex), (211 : Vertex), (214 : Vertex), (220 : Vertex), (223 : Vertex), (259 : Vertex), (261 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (276 : Vertex), (279 : Vertex), (280 : Vertex), (283 : Vertex), (421 : Vertex), (426 : Vertex), (428 : Vertex), (436 : Vertex), (439 : Vertex), (440 : Vertex), (443 : Vertex), (453 : Vertex), (468 : Vertex), (471 : Vertex), (475 : Vertex), (496 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (5 : Vertex), (9 : Vertex), (10 : Vertex), (12 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (24 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (68 : Vertex), (78 : Vertex), (80 : Vertex), (85 : Vertex), (89 : Vertex), (95 : Vertex), (130 : Vertex), (132 : Vertex), (139 : Vertex), (142 : Vertex), (144 : Vertex), (149 : Vertex), (153 : Vertex), (159 : Vertex), (192 : Vertex), (195 : Vertex), (197 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (216 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (260 : Vertex), (267 : Vertex), (270 : Vertex), (272 : Vertex), (277 : Vertex), (278 : Vertex), (281 : Vertex), (287 : Vertex), (418 : Vertex), (420 : Vertex), (430 : Vertex), (432 : Vertex), (437 : Vertex), (441 : Vertex), (447 : Vertex), (459 : Vertex), (464 : Vertex), (469 : Vertex), (473 : Vertex), (479 : Vertex), (480 : Vertex), (497 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (2 : Vertex), (3 : Vertex), (5 : Vertex), (7 : Vertex), (9 : Vertex), (10 : Vertex), (12 : Vertex), (13 : Vertex), (14 : Vertex), (15 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (24 : Vertex), (25 : Vertex), (26 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (66 : Vertex), (67 : Vertex), (68 : Vertex), (73 : Vertex), (74 : Vertex), (76 : Vertex), (78 : Vertex), (80 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (89 : Vertex), (91 : Vertex), (95 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (203 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (216 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (223 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (270 : Vertex), (272 : Vertex), (276 : Vertex), (277 : Vertex), (278 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (420 : Vertex), (421 : Vertex), (426 : Vertex), (428 : Vertex), (430 : Vertex), (432 : Vertex), (436 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (443 : Vertex), (447 : Vertex), (453 : Vertex), (459 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex), (480 : Vertex), (496 : Vertex), (497 : Vertex)]
def head : Vertex := 418
def ban : Nat := 13407194164390617696365054455594081838870593673637889917859904210831527447220880018262223216759512414134801689501293093788190590631224545038817550855571792
def reachable : Nat := 613765551979403208970542611764288608772146954503459863657232890236582852666958539651081407391013555230168685192957065563292180722024907616098150512303
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
theorem oddSide_length : oddSide.length = 58 := by decide
theorem evenSide_length : evenSide.length = 59 := by decide

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

end Snake9.Regrowth.E112217
