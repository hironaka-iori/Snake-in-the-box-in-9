import RegrowthParityCounts
namespace Snake9.Regrowth.E112095
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[84, 85, 69, 71, 70, 78, 74, 72, 73, 89, 91, 83, 82, 18, 26, 24, 28, 156, 148, 149, 133, 135, 134, 130, 138, 136, 137, 153, 155, 147, 403, 387, 385, 384, 400, 408, 410, 414, 398, 399, 397, 413, 477, 473, 457, 456, 458, 450, 466, 498, 242, 243, 251, 249, 233, 232, 234, 238, 230, 231, 229, 245, 244, 252, 508, 380, 372, 373, 357, 359, 358, 354, 362, 360, 361, 377, 379, 371, 307, 291, 289, 288, 304, 312, 314, 318, 302, 303, 301, 317, 61, 57, 41, 40, 42, 34, 38, 36, 100, 108, 109, 111, 107, 99, 97, 113, 112, 120, 122, 126, 118, 119]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (11 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (23 : Vertex), (31 : Vertex), (55 : Vertex), (119 : Vertex), (160 : Vertex), (161 : Vertex), (163 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (186 : Vertex), (190 : Vertex), (191 : Vertex), (192 : Vertex), (193 : Vertex), (195 : Vertex), (196 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (214 : Vertex), (215 : Vertex), (216 : Vertex), (218 : Vertex), (222 : Vertex), (223 : Vertex), (258 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (273 : Vertex), (276 : Vertex), (277 : Vertex), (278 : Vertex), (279 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (323 : Vertex), (324 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (346 : Vertex), (350 : Vertex), (351 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (433 : Vertex), (436 : Vertex), (437 : Vertex), (438 : Vertex), (439 : Vertex), (441 : Vertex), (443 : Vertex), (447 : Vertex), (452 : Vertex), (453 : Vertex), (455 : Vertex), (468 : Vertex), (471 : Vertex), (480 : Vertex), (481 : Vertex), (483 : Vertex), (484 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (503 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (11 : Vertex), (13 : Vertex), (31 : Vertex), (55 : Vertex), (161 : Vertex), (171 : Vertex), (173 : Vertex), (176 : Vertex), (182 : Vertex), (186 : Vertex), (191 : Vertex), (193 : Vertex), (196 : Vertex), (203 : Vertex), (205 : Vertex), (208 : Vertex), (214 : Vertex), (218 : Vertex), (223 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (268 : Vertex), (273 : Vertex), (276 : Vertex), (279 : Vertex), (283 : Vertex), (321 : Vertex), (324 : Vertex), (331 : Vertex), (333 : Vertex), (336 : Vertex), (342 : Vertex), (346 : Vertex), (351 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (428 : Vertex), (433 : Vertex), (436 : Vertex), (439 : Vertex), (443 : Vertex), (453 : Vertex), (468 : Vertex), (471 : Vertex), (481 : Vertex), (484 : Vertex), (491 : Vertex), (493 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (15 : Vertex), (17 : Vertex), (23 : Vertex), (119 : Vertex), (160 : Vertex), (163 : Vertex), (172 : Vertex), (175 : Vertex), (177 : Vertex), (183 : Vertex), (184 : Vertex), (190 : Vertex), (192 : Vertex), (195 : Vertex), (204 : Vertex), (207 : Vertex), (209 : Vertex), (215 : Vertex), (216 : Vertex), (222 : Vertex), (258 : Vertex), (260 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (277 : Vertex), (278 : Vertex), (281 : Vertex), (287 : Vertex), (320 : Vertex), (323 : Vertex), (332 : Vertex), (335 : Vertex), (337 : Vertex), (343 : Vertex), (344 : Vertex), (350 : Vertex), (418 : Vertex), (420 : Vertex), (423 : Vertex), (424 : Vertex), (427 : Vertex), (437 : Vertex), (438 : Vertex), (441 : Vertex), (447 : Vertex), (452 : Vertex), (455 : Vertex), (480 : Vertex), (483 : Vertex), (495 : Vertex), (497 : Vertex), (503 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (3 : Vertex), (11 : Vertex), (13 : Vertex), (15 : Vertex), (17 : Vertex), (23 : Vertex), (31 : Vertex), (55 : Vertex), (160 : Vertex), (161 : Vertex), (163 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (186 : Vertex), (190 : Vertex), (191 : Vertex), (192 : Vertex), (193 : Vertex), (195 : Vertex), (196 : Vertex), (203 : Vertex), (204 : Vertex), (205 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (214 : Vertex), (215 : Vertex), (216 : Vertex), (218 : Vertex), (222 : Vertex), (223 : Vertex), (258 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (268 : Vertex), (273 : Vertex), (276 : Vertex), (277 : Vertex), (278 : Vertex), (279 : Vertex), (281 : Vertex), (283 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (323 : Vertex), (324 : Vertex), (331 : Vertex), (332 : Vertex), (333 : Vertex), (335 : Vertex), (336 : Vertex), (337 : Vertex), (342 : Vertex), (343 : Vertex), (344 : Vertex), (346 : Vertex), (350 : Vertex), (351 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (426 : Vertex), (427 : Vertex), (428 : Vertex), (433 : Vertex), (436 : Vertex), (437 : Vertex), (438 : Vertex), (439 : Vertex), (441 : Vertex), (443 : Vertex), (447 : Vertex), (452 : Vertex), (453 : Vertex), (455 : Vertex), (468 : Vertex), (471 : Vertex), (480 : Vertex), (481 : Vertex), (483 : Vertex), (484 : Vertex), (491 : Vertex), (493 : Vertex), (495 : Vertex), (497 : Vertex), (503 : Vertex), (511 : Vertex)]
def head : Vertex := 119
def ban : Nat := 6677173321826420109269862608751227442679742000924926252004345615906639395625386666245775024882922107894141651161656476004827551526715214203837566834006004
def reachable : Nat := 6730634608116176990304162389454618684799623819667467125719215827815124634448160310556099273283981319795890207024829574848926331285231355742596082172078091
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
theorem oddSide_length : oddSide.length = 54 := by decide
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

end Snake9.Regrowth.E112095
