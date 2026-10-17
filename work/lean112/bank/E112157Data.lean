import RegrowthParityCounts
namespace Snake9.Regrowth.E112157
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[13, 12, 28, 30, 31, 27, 19, 17, 21, 85, 84, 86, 82, 90, 88, 89, 73, 65, 67, 71, 79, 78, 206, 462, 463, 455, 451, 449, 457, 456, 472, 474, 466, 470, 468, 469, 477, 221, 253, 249, 248, 250, 242, 246, 230, 166, 162, 160, 168, 172, 188, 190, 191, 187, 179, 177, 181, 437, 436, 438, 434, 442, 440, 441, 425, 417, 419, 423, 431, 430, 302, 366, 367, 359, 355, 353, 361, 360, 376, 378, 370, 374, 372, 373, 381, 317, 319, 315, 307, 305, 304, 288, 292, 36, 52, 54, 55, 39, 35, 33, 41, 57, 56, 58, 42, 106, 98, 96, 112, 113, 115, 123]
def region : List Vertex := [(0 : Vertex), (2 : Vertex), (6 : Vertex), (101 : Vertex), (108 : Vertex), (109 : Vertex), (123 : Vertex), (124 : Vertex), (126 : Vertex), (127 : Vertex), (129 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (135 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (143 : Vertex), (144 : Vertex), (146 : Vertex), (148 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (154 : Vertex), (192 : Vertex), (194 : Vertex), (196 : Vertex), (197 : Vertex), (203 : Vertex), (208 : Vertex), (209 : Vertex), (211 : Vertex), (215 : Vertex), (219 : Vertex), (225 : Vertex), (227 : Vertex), (229 : Vertex), (235 : Vertex), (239 : Vertex), (257 : Vertex), (258 : Vertex), (259 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (271 : Vertex), (274 : Vertex), (276 : Vertex), (278 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (320 : Vertex), (322 : Vertex), (324 : Vertex), (325 : Vertex), (326 : Vertex), (330 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (336 : Vertex), (337 : Vertex), (339 : Vertex), (343 : Vertex), (347 : Vertex), (348 : Vertex), (350 : Vertex), (351 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (394 : Vertex), (395 : Vertex), (396 : Vertex), (397 : Vertex), (400 : Vertex), (401 : Vertex), (403 : Vertex), (407 : Vertex), (411 : Vertex), (412 : Vertex), (414 : Vertex), (415 : Vertex), (480 : Vertex), (482 : Vertex), (484 : Vertex), (485 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (496 : Vertex), (497 : Vertex), (499 : Vertex), (503 : Vertex), (507 : Vertex), (508 : Vertex), (510 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(2 : Vertex), (109 : Vertex), (124 : Vertex), (127 : Vertex), (131 : Vertex), (133 : Vertex), (137 : Vertex), (138 : Vertex), (143 : Vertex), (146 : Vertex), (148 : Vertex), (151 : Vertex), (152 : Vertex), (194 : Vertex), (196 : Vertex), (203 : Vertex), (208 : Vertex), (211 : Vertex), (227 : Vertex), (229 : Vertex), (239 : Vertex), (259 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (271 : Vertex), (274 : Vertex), (276 : Vertex), (279 : Vertex), (280 : Vertex), (322 : Vertex), (324 : Vertex), (331 : Vertex), (333 : Vertex), (336 : Vertex), (339 : Vertex), (348 : Vertex), (351 : Vertex), (386 : Vertex), (388 : Vertex), (395 : Vertex), (397 : Vertex), (400 : Vertex), (403 : Vertex), (412 : Vertex), (415 : Vertex), (482 : Vertex), (484 : Vertex), (491 : Vertex), (493 : Vertex), (496 : Vertex), (499 : Vertex), (508 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (101 : Vertex), (108 : Vertex), (123 : Vertex), (126 : Vertex), (129 : Vertex), (132 : Vertex), (135 : Vertex), (139 : Vertex), (144 : Vertex), (150 : Vertex), (153 : Vertex), (154 : Vertex), (192 : Vertex), (197 : Vertex), (209 : Vertex), (215 : Vertex), (219 : Vertex), (225 : Vertex), (235 : Vertex), (257 : Vertex), (258 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (278 : Vertex), (281 : Vertex), (282 : Vertex), (320 : Vertex), (325 : Vertex), (326 : Vertex), (330 : Vertex), (332 : Vertex), (337 : Vertex), (343 : Vertex), (347 : Vertex), (350 : Vertex), (384 : Vertex), (389 : Vertex), (390 : Vertex), (394 : Vertex), (396 : Vertex), (401 : Vertex), (407 : Vertex), (411 : Vertex), (414 : Vertex), (480 : Vertex), (485 : Vertex), (490 : Vertex), (492 : Vertex), (497 : Vertex), (503 : Vertex), (507 : Vertex), (510 : Vertex)]
def others : List Vertex := [(0 : Vertex), (2 : Vertex), (6 : Vertex), (101 : Vertex), (108 : Vertex), (109 : Vertex), (124 : Vertex), (126 : Vertex), (127 : Vertex), (129 : Vertex), (131 : Vertex), (132 : Vertex), (133 : Vertex), (135 : Vertex), (137 : Vertex), (138 : Vertex), (139 : Vertex), (143 : Vertex), (144 : Vertex), (146 : Vertex), (148 : Vertex), (150 : Vertex), (151 : Vertex), (152 : Vertex), (153 : Vertex), (154 : Vertex), (192 : Vertex), (194 : Vertex), (196 : Vertex), (197 : Vertex), (203 : Vertex), (208 : Vertex), (209 : Vertex), (211 : Vertex), (215 : Vertex), (219 : Vertex), (225 : Vertex), (227 : Vertex), (229 : Vertex), (235 : Vertex), (239 : Vertex), (257 : Vertex), (258 : Vertex), (259 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (271 : Vertex), (274 : Vertex), (276 : Vertex), (278 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (320 : Vertex), (322 : Vertex), (324 : Vertex), (325 : Vertex), (326 : Vertex), (330 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (336 : Vertex), (337 : Vertex), (339 : Vertex), (343 : Vertex), (347 : Vertex), (348 : Vertex), (350 : Vertex), (351 : Vertex), (384 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (394 : Vertex), (395 : Vertex), (396 : Vertex), (397 : Vertex), (400 : Vertex), (401 : Vertex), (403 : Vertex), (407 : Vertex), (411 : Vertex), (412 : Vertex), (414 : Vertex), (415 : Vertex), (480 : Vertex), (482 : Vertex), (484 : Vertex), (485 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (496 : Vertex), (497 : Vertex), (499 : Vertex), (503 : Vertex), (507 : Vertex), (508 : Vertex), (510 : Vertex), (511 : Vertex)]
def head : Vertex := 123
def ban : Nat := 2066484292637027043924439535777223255894900649276698748297546080485087364392897777770436639672227190280654953819959128649940933155887154625872254805737402
def reachable : Nat := 11341323637305570055649585462428622871584465171315694629426015363236676665680649199031437658494676237409376904366526922203812949656059415320561394200346693
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
theorem evenSide_length : evenSide.length = 55 := by decide

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

end Snake9.Regrowth.E112157
