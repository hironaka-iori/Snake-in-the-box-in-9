import RegrowthParityCounts
namespace Snake9.Regrowth.E112090
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 4, 6, 14, 10, 26, 24, 25, 29, 21, 23, 19, 83, 82, 80, 84, 92, 94, 95, 79, 71, 69, 65, 73, 72, 200, 456, 457, 449, 453, 455, 463, 462, 478, 476, 468, 464, 466, 467, 475, 219, 251, 255, 254, 252, 244, 240, 224, 160, 164, 166, 174, 170, 186, 184, 185, 189, 181, 183, 179, 435, 434, 432, 436, 444, 446, 447, 431, 423, 421, 417, 425, 424, 296, 360, 361, 353, 357, 359, 367, 366, 382, 380, 372, 368, 370, 371, 379, 315, 313, 317, 309, 311, 310, 294, 290, 34, 50, 48, 49, 33, 37, 39, 47, 63, 62, 60, 44, 108, 100, 102, 118]
def region : List Vertex := [(99 : Vertex), (106 : Vertex), (107 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (120 : Vertex), (121 : Vertex), (122 : Vertex), (125 : Vertex), (129 : Vertex), (130 : Vertex), (131 : Vertex), (133 : Vertex), (135 : Vertex), (137 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (150 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (194 : Vertex), (195 : Vertex), (196 : Vertex), (198 : Vertex), (205 : Vertex), (209 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (221 : Vertex), (227 : Vertex), (229 : Vertex), (231 : Vertex), (233 : Vertex), (237 : Vertex), (257 : Vertex), (259 : Vertex), (261 : Vertex), (263 : Vertex), (265 : Vertex), (267 : Vertex), (268 : Vertex), (269 : Vertex), (271 : Vertex), (272 : Vertex), (273 : Vertex), (274 : Vertex), (276 : Vertex), (284 : Vertex), (286 : Vertex), (287 : Vertex), (320 : Vertex), (322 : Vertex), (323 : Vertex), (324 : Vertex), (326 : Vertex), (330 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (337 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (346 : Vertex), (349 : Vertex), (384 : Vertex), (386 : Vertex), (387 : Vertex), (388 : Vertex), (390 : Vertex), (394 : Vertex), (395 : Vertex), (396 : Vertex), (397 : Vertex), (401 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (413 : Vertex), (482 : Vertex), (483 : Vertex), (484 : Vertex), (486 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (497 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (506 : Vertex), (509 : Vertex)]
def oddSide : List Vertex := [(107 : Vertex), (117 : Vertex), (118 : Vertex), (121 : Vertex), (122 : Vertex), (131 : Vertex), (133 : Vertex), (137 : Vertex), (140 : Vertex), (143 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (158 : Vertex), (194 : Vertex), (196 : Vertex), (205 : Vertex), (213 : Vertex), (214 : Vertex), (227 : Vertex), (229 : Vertex), (233 : Vertex), (259 : Vertex), (261 : Vertex), (265 : Vertex), (268 : Vertex), (271 : Vertex), (273 : Vertex), (274 : Vertex), (276 : Vertex), (286 : Vertex), (322 : Vertex), (324 : Vertex), (331 : Vertex), (333 : Vertex), (341 : Vertex), (342 : Vertex), (345 : Vertex), (346 : Vertex), (386 : Vertex), (388 : Vertex), (395 : Vertex), (397 : Vertex), (405 : Vertex), (406 : Vertex), (409 : Vertex), (410 : Vertex), (482 : Vertex), (484 : Vertex), (491 : Vertex), (493 : Vertex), (501 : Vertex), (502 : Vertex), (505 : Vertex), (506 : Vertex)]
def evenSide : List Vertex := [(99 : Vertex), (106 : Vertex), (119 : Vertex), (120 : Vertex), (125 : Vertex), (129 : Vertex), (130 : Vertex), (135 : Vertex), (139 : Vertex), (141 : Vertex), (144 : Vertex), (150 : Vertex), (156 : Vertex), (159 : Vertex), (195 : Vertex), (198 : Vertex), (209 : Vertex), (215 : Vertex), (221 : Vertex), (231 : Vertex), (237 : Vertex), (257 : Vertex), (263 : Vertex), (267 : Vertex), (269 : Vertex), (272 : Vertex), (284 : Vertex), (287 : Vertex), (320 : Vertex), (323 : Vertex), (326 : Vertex), (330 : Vertex), (332 : Vertex), (337 : Vertex), (343 : Vertex), (344 : Vertex), (349 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (394 : Vertex), (396 : Vertex), (401 : Vertex), (407 : Vertex), (408 : Vertex), (413 : Vertex), (483 : Vertex), (486 : Vertex), (490 : Vertex), (492 : Vertex), (497 : Vertex), (503 : Vertex), (504 : Vertex), (509 : Vertex)]
def others : List Vertex := [(99 : Vertex), (106 : Vertex), (107 : Vertex), (117 : Vertex), (119 : Vertex), (120 : Vertex), (121 : Vertex), (122 : Vertex), (125 : Vertex), (129 : Vertex), (130 : Vertex), (131 : Vertex), (133 : Vertex), (135 : Vertex), (137 : Vertex), (139 : Vertex), (140 : Vertex), (141 : Vertex), (143 : Vertex), (144 : Vertex), (145 : Vertex), (146 : Vertex), (148 : Vertex), (150 : Vertex), (156 : Vertex), (158 : Vertex), (159 : Vertex), (194 : Vertex), (195 : Vertex), (196 : Vertex), (198 : Vertex), (205 : Vertex), (209 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (221 : Vertex), (227 : Vertex), (229 : Vertex), (231 : Vertex), (233 : Vertex), (237 : Vertex), (257 : Vertex), (259 : Vertex), (261 : Vertex), (263 : Vertex), (265 : Vertex), (267 : Vertex), (268 : Vertex), (269 : Vertex), (271 : Vertex), (272 : Vertex), (273 : Vertex), (274 : Vertex), (276 : Vertex), (284 : Vertex), (286 : Vertex), (287 : Vertex), (320 : Vertex), (322 : Vertex), (323 : Vertex), (324 : Vertex), (326 : Vertex), (330 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (337 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (345 : Vertex), (346 : Vertex), (349 : Vertex), (384 : Vertex), (386 : Vertex), (387 : Vertex), (388 : Vertex), (390 : Vertex), (394 : Vertex), (395 : Vertex), (396 : Vertex), (397 : Vertex), (401 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (413 : Vertex), (482 : Vertex), (483 : Vertex), (484 : Vertex), (486 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (497 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (504 : Vertex), (505 : Vertex), (506 : Vertex), (509 : Vertex)]
def head : Vertex := 118
def ban : Nat := 11318927311020272086059899014450974274330895598036958727585145767607818367651668286851330589852668525342825458340168726136935702421459467856879587004776447
def reachable : Nat := 2088880618922325013514125983754871853148470222555434650138415676113945662421878689950543708314234902347206399846317324716818180390487102089554062001307648
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
theorem oddSide_length : oddSide.length = 55 := by decide
theorem evenSide_length : evenSide.length = 54 := by decide

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

end Snake9.Regrowth.E112090
