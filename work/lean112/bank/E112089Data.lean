import RegrowthParityCounts
namespace Snake9.Regrowth.E112089
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[262, 260, 276, 277, 279, 287, 271, 303, 367, 366, 358, 356, 372, 373, 375, 371, 379, 378, 376, 360, 361, 353, 289, 417, 425, 424, 440, 442, 443, 447, 439, 437, 436, 420, 422, 430, 174, 190, 188, 189, 173, 165, 167, 163, 179, 178, 176, 160, 224, 228, 244, 245, 247, 255, 251, 249, 505, 497, 496, 498, 502, 510, 508, 492, 493, 485, 487, 483, 491, 490, 234, 106, 107, 99, 103, 101, 109, 125, 124, 126, 118, 114, 112, 113, 49, 53, 55, 63, 59, 58, 56, 40, 44, 36, 38, 34, 290, 306, 310, 318, 316, 317, 313, 281, 345, 337, 336, 338, 342, 350, 348, 332]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (5 : Vertex), (7 : Vertex), (9 : Vertex), (10 : Vertex), (11 : Vertex), (13 : Vertex), (14 : Vertex), (16 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (64 : Vertex), (65 : Vertex), (66 : Vertex), (68 : Vertex), (70 : Vertex), (72 : Vertex), (73 : Vertex), (76 : Vertex), (78 : Vertex), (79 : Vertex), (83 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (90 : Vertex), (91 : Vertex), (95 : Vertex), (129 : Vertex), (130 : Vertex), (132 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (143 : Vertex), (145 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (206 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (216 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (259 : Vertex), (264 : Vertex), (266 : Vertex), (282 : Vertex), (323 : Vertex), (325 : Vertex), (327 : Vertex), (330 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (384 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (391 : Vertex), (394 : Vertex), (395 : Vertex), (396 : Vertex), (397 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (448 : Vertex), (449 : Vertex), (450 : Vertex), (452 : Vertex), (454 : Vertex), (456 : Vertex), (457 : Vertex), (462 : Vertex), (463 : Vertex), (467 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (11 : Vertex), (13 : Vertex), (14 : Vertex), (16 : Vertex), (19 : Vertex), (22 : Vertex), (28 : Vertex), (64 : Vertex), (70 : Vertex), (73 : Vertex), (76 : Vertex), (79 : Vertex), (84 : Vertex), (87 : Vertex), (88 : Vertex), (91 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (143 : Vertex), (145 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (155 : Vertex), (193 : Vertex), (194 : Vertex), (199 : Vertex), (200 : Vertex), (203 : Vertex), (205 : Vertex), (206 : Vertex), (208 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (259 : Vertex), (266 : Vertex), (327 : Vertex), (331 : Vertex), (333 : Vertex), (386 : Vertex), (391 : Vertex), (395 : Vertex), (397 : Vertex), (400 : Vertex), (403 : Vertex), (406 : Vertex), (412 : Vertex), (448 : Vertex), (454 : Vertex), (457 : Vertex), (463 : Vertex), (468 : Vertex), (471 : Vertex), (472 : Vertex), (475 : Vertex), (477 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (5 : Vertex), (9 : Vertex), (10 : Vertex), (18 : Vertex), (29 : Vertex), (30 : Vertex), (65 : Vertex), (66 : Vertex), (68 : Vertex), (72 : Vertex), (78 : Vertex), (83 : Vertex), (85 : Vertex), (90 : Vertex), (95 : Vertex), (129 : Vertex), (130 : Vertex), (132 : Vertex), (136 : Vertex), (139 : Vertex), (149 : Vertex), (150 : Vertex), (153 : Vertex), (154 : Vertex), (159 : Vertex), (195 : Vertex), (197 : Vertex), (198 : Vertex), (201 : Vertex), (204 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (216 : Vertex), (221 : Vertex), (222 : Vertex), (264 : Vertex), (282 : Vertex), (323 : Vertex), (325 : Vertex), (330 : Vertex), (332 : Vertex), (384 : Vertex), (387 : Vertex), (389 : Vertex), (394 : Vertex), (396 : Vertex), (401 : Vertex), (402 : Vertex), (413 : Vertex), (414 : Vertex), (449 : Vertex), (450 : Vertex), (452 : Vertex), (456 : Vertex), (462 : Vertex), (467 : Vertex), (469 : Vertex), (474 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (5 : Vertex), (7 : Vertex), (9 : Vertex), (10 : Vertex), (11 : Vertex), (13 : Vertex), (14 : Vertex), (16 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (64 : Vertex), (65 : Vertex), (66 : Vertex), (68 : Vertex), (70 : Vertex), (72 : Vertex), (73 : Vertex), (76 : Vertex), (78 : Vertex), (79 : Vertex), (83 : Vertex), (84 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (90 : Vertex), (91 : Vertex), (95 : Vertex), (129 : Vertex), (130 : Vertex), (132 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (140 : Vertex), (143 : Vertex), (145 : Vertex), (148 : Vertex), (149 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (197 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (206 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (216 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (259 : Vertex), (264 : Vertex), (266 : Vertex), (282 : Vertex), (323 : Vertex), (325 : Vertex), (327 : Vertex), (330 : Vertex), (331 : Vertex), (333 : Vertex), (384 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (391 : Vertex), (394 : Vertex), (395 : Vertex), (396 : Vertex), (397 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (448 : Vertex), (449 : Vertex), (450 : Vertex), (452 : Vertex), (454 : Vertex), (456 : Vertex), (457 : Vertex), (462 : Vertex), (463 : Vertex), (467 : Vertex), (468 : Vertex), (469 : Vertex), (471 : Vertex), (472 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex), (479 : Vertex)]
def head : Vertex := 332
def ban : Nat := 13407807927824176940146789634259539096967732959346265511519656002831181606681898515802255294551532621026395236135551274414328158869236532499372986040750420
def reachable : Nat := 2118420159427235363946307030511632861246127866203905440890582423391648460999619003615370806663636622050934776439425723942710037447060662965333675
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

end Snake9.Regrowth.E112089
