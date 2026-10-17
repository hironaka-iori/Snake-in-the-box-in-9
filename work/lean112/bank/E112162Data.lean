import RegrowthParityCounts
namespace Snake9.Regrowth.E112162
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 2, 6, 262, 278, 274, 282, 280, 281, 285, 317, 381, 373, 372, 374, 370, 378, 376, 360, 361, 353, 355, 359, 367, 366, 302, 430, 431, 423, 419, 417, 425, 441, 440, 442, 434, 438, 436, 437, 181, 177, 179, 187, 191, 190, 188, 172, 168, 160, 162, 166, 230, 246, 242, 250, 248, 249, 233, 235, 491, 490, 482, 480, 496, 497, 499, 503, 511, 510, 508, 492, 493, 485, 229, 101, 109, 108, 124, 126, 127, 123, 115, 113, 112, 96, 98, 106, 42, 58, 56, 57, 41, 33, 35, 39, 55, 54, 52, 36, 292, 288, 304, 305, 307, 315, 299, 267, 331, 330, 322, 320, 336]
def region : List Vertex := [(5 : Vertex), (12 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (19 : Vertex), (21 : Vertex), (27 : Vertex), (28 : Vertex), (30 : Vertex), (31 : Vertex), (65 : Vertex), (67 : Vertex), (68 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (78 : Vertex), (79 : Vertex), (82 : Vertex), (84 : Vertex), (85 : Vertex), (86 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (90 : Vertex), (93 : Vertex), (129 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (135 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex), (143 : Vertex), (144 : Vertex), (146 : Vertex), (148 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (154 : Vertex), (157 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (196 : Vertex), (199 : Vertex), (200 : Vertex), (202 : Vertex), (204 : Vertex), (205 : Vertex), (206 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (211 : Vertex), (212 : Vertex), (213 : Vertex), (215 : Vertex), (219 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (223 : Vertex), (257 : Vertex), (261 : Vertex), (268 : Vertex), (325 : Vertex), (332 : Vertex), (333 : Vertex), (336 : Vertex), (337 : Vertex), (339 : Vertex), (343 : Vertex), (348 : Vertex), (350 : Vertex), (351 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (392 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (400 : Vertex), (401 : Vertex), (403 : Vertex), (407 : Vertex), (411 : Vertex), (412 : Vertex), (414 : Vertex), (415 : Vertex), (449 : Vertex), (451 : Vertex), (452 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (462 : Vertex), (463 : Vertex), (466 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (472 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex)]
def oddSide : List Vertex := [(13 : Vertex), (19 : Vertex), (21 : Vertex), (28 : Vertex), (31 : Vertex), (67 : Vertex), (73 : Vertex), (79 : Vertex), (82 : Vertex), (84 : Vertex), (87 : Vertex), (88 : Vertex), (93 : Vertex), (131 : Vertex), (133 : Vertex), (137 : Vertex), (138 : Vertex), (143 : Vertex), (146 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (157 : Vertex), (193 : Vertex), (194 : Vertex), (196 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (206 : Vertex), (208 : Vertex), (211 : Vertex), (213 : Vertex), (220 : Vertex), (223 : Vertex), (261 : Vertex), (268 : Vertex), (333 : Vertex), (336 : Vertex), (339 : Vertex), (348 : Vertex), (351 : Vertex), (386 : Vertex), (388 : Vertex), (392 : Vertex), (397 : Vertex), (400 : Vertex), (403 : Vertex), (412 : Vertex), (415 : Vertex), (451 : Vertex), (454 : Vertex), (457 : Vertex), (463 : Vertex), (466 : Vertex), (468 : Vertex), (472 : Vertex), (475 : Vertex), (477 : Vertex)]
def evenSide : List Vertex := [(5 : Vertex), (12 : Vertex), (15 : Vertex), (17 : Vertex), (27 : Vertex), (30 : Vertex), (65 : Vertex), (68 : Vertex), (71 : Vertex), (72 : Vertex), (78 : Vertex), (85 : Vertex), (86 : Vertex), (89 : Vertex), (90 : Vertex), (129 : Vertex), (132 : Vertex), (135 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex), (144 : Vertex), (150 : Vertex), (153 : Vertex), (154 : Vertex), (192 : Vertex), (195 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (209 : Vertex), (212 : Vertex), (215 : Vertex), (219 : Vertex), (221 : Vertex), (222 : Vertex), (257 : Vertex), (325 : Vertex), (332 : Vertex), (337 : Vertex), (343 : Vertex), (350 : Vertex), (384 : Vertex), (389 : Vertex), (394 : Vertex), (396 : Vertex), (401 : Vertex), (407 : Vertex), (411 : Vertex), (414 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex), (456 : Vertex), (462 : Vertex), (469 : Vertex), (470 : Vertex), (473 : Vertex), (474 : Vertex)]
def others : List Vertex := [(5 : Vertex), (12 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (19 : Vertex), (21 : Vertex), (27 : Vertex), (28 : Vertex), (30 : Vertex), (31 : Vertex), (65 : Vertex), (67 : Vertex), (68 : Vertex), (71 : Vertex), (72 : Vertex), (73 : Vertex), (78 : Vertex), (79 : Vertex), (82 : Vertex), (84 : Vertex), (85 : Vertex), (86 : Vertex), (87 : Vertex), (88 : Vertex), (89 : Vertex), (90 : Vertex), (93 : Vertex), (129 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (135 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex), (143 : Vertex), (144 : Vertex), (146 : Vertex), (148 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (154 : Vertex), (157 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (196 : Vertex), (199 : Vertex), (200 : Vertex), (202 : Vertex), (204 : Vertex), (205 : Vertex), (206 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (211 : Vertex), (212 : Vertex), (213 : Vertex), (215 : Vertex), (219 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (223 : Vertex), (257 : Vertex), (261 : Vertex), (268 : Vertex), (325 : Vertex), (332 : Vertex), (333 : Vertex), (337 : Vertex), (339 : Vertex), (343 : Vertex), (348 : Vertex), (350 : Vertex), (351 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (392 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (400 : Vertex), (401 : Vertex), (403 : Vertex), (407 : Vertex), (411 : Vertex), (412 : Vertex), (414 : Vertex), (415 : Vertex), (449 : Vertex), (451 : Vertex), (452 : Vertex), (454 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (462 : Vertex), (463 : Vertex), (466 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (472 : Vertex), (473 : Vertex), (474 : Vertex), (475 : Vertex), (477 : Vertex)]
def head : Vertex := 336
def ban : Nat := 13407807929363901578518778886585436394119917827851813392364776317049276469574366547182424330595917597586895652091169705045599578024392086116081418441674719
def reachable : Nat := 578695521055246111620409733359447992740579985358785126672487560499180429619449967570985830103136206095316345808154304787554483830352230564409376
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

end Snake9.Regrowth.E112162
