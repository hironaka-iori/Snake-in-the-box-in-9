import RegrowthParityCounts
namespace Snake9.Regrowth.E112228
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 4, 68, 69, 77, 79, 95, 94, 92, 88, 80, 81, 83, 67, 66, 74, 10, 138, 130, 131, 147, 145, 144, 148, 156, 158, 159, 143, 141, 133, 389, 405, 407, 406, 390, 398, 396, 392, 408, 409, 411, 395, 459, 463, 479, 478, 476, 468, 452, 484, 228, 229, 237, 239, 255, 254, 252, 248, 240, 241, 243, 227, 226, 234, 490, 362, 354, 355, 371, 369, 368, 372, 380, 382, 383, 367, 365, 357, 293, 309, 311, 310, 294, 302, 300, 296, 312, 313, 315, 299, 43, 47, 63, 62, 60, 52, 48, 50, 18, 22, 23, 21, 29, 25, 9, 265, 269, 271, 263, 259, 275, 273]
def region : List Vertex := [(33 : Vertex), (96 : Vertex), (97 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (108 : Vertex), (110 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (172 : Vertex), (174 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (204 : Vertex), (206 : Vertex), (210 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (272 : Vertex), (273 : Vertex), (276 : Vertex), (282 : Vertex), (284 : Vertex), (286 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (328 : Vertex), (332 : Vertex), (334 : Vertex), (338 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (349 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (419 : Vertex), (423 : Vertex), (425 : Vertex), (429 : Vertex), (431 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (442 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (447 : Vertex), (449 : Vertex), (450 : Vertex), (465 : Vertex), (466 : Vertex), (467 : Vertex), (481 : Vertex), (487 : Vertex), (489 : Vertex), (498 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (505 : Vertex), (507 : Vertex), (509 : Vertex)]
def oddSide : List Vertex := [(97 : Vertex), (103 : Vertex), (104 : Vertex), (110 : Vertex), (117 : Vertex), (118 : Vertex), (121 : Vertex), (122 : Vertex), (161 : Vertex), (167 : Vertex), (168 : Vertex), (174 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (206 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (273 : Vertex), (276 : Vertex), (286 : Vertex), (321 : Vertex), (328 : Vertex), (334 : Vertex), (341 : Vertex), (342 : Vertex), (345 : Vertex), (346 : Vertex), (416 : Vertex), (419 : Vertex), (425 : Vertex), (431 : Vertex), (433 : Vertex), (434 : Vertex), (436 : Vertex), (445 : Vertex), (446 : Vertex), (465 : Vertex), (466 : Vertex), (481 : Vertex), (487 : Vertex), (501 : Vertex), (502 : Vertex), (505 : Vertex)]
def evenSide : List Vertex := [(33 : Vertex), (96 : Vertex), (102 : Vertex), (105 : Vertex), (108 : Vertex), (119 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (166 : Vertex), (169 : Vertex), (172 : Vertex), (183 : Vertex), (187 : Vertex), (189 : Vertex), (192 : Vertex), (198 : Vertex), (201 : Vertex), (204 : Vertex), (210 : Vertex), (215 : Vertex), (219 : Vertex), (221 : Vertex), (272 : Vertex), (282 : Vertex), (284 : Vertex), (320 : Vertex), (326 : Vertex), (332 : Vertex), (338 : Vertex), (343 : Vertex), (347 : Vertex), (349 : Vertex), (417 : Vertex), (418 : Vertex), (423 : Vertex), (429 : Vertex), (432 : Vertex), (435 : Vertex), (442 : Vertex), (444 : Vertex), (447 : Vertex), (449 : Vertex), (450 : Vertex), (467 : Vertex), (489 : Vertex), (498 : Vertex), (503 : Vertex), (507 : Vertex), (509 : Vertex)]
def others : List Vertex := [(33 : Vertex), (96 : Vertex), (97 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (105 : Vertex), (108 : Vertex), (110 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (125 : Vertex), (160 : Vertex), (161 : Vertex), (166 : Vertex), (167 : Vertex), (168 : Vertex), (169 : Vertex), (172 : Vertex), (174 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (204 : Vertex), (206 : Vertex), (210 : Vertex), (213 : Vertex), (214 : Vertex), (215 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (272 : Vertex), (276 : Vertex), (282 : Vertex), (284 : Vertex), (286 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (328 : Vertex), (332 : Vertex), (334 : Vertex), (338 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (349 : Vertex), (416 : Vertex), (417 : Vertex), (418 : Vertex), (419 : Vertex), (423 : Vertex), (425 : Vertex), (429 : Vertex), (431 : Vertex), (432 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (436 : Vertex), (442 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (447 : Vertex), (449 : Vertex), (450 : Vertex), (465 : Vertex), (466 : Vertex), (467 : Vertex), (481 : Vertex), (487 : Vertex), (489 : Vertex), (498 : Vertex), (501 : Vertex), (502 : Vertex), (503 : Vertex), (505 : Vertex), (507 : Vertex), (509 : Vertex)]
def head : Vertex := 273
def ban : Nat := 11161441621110633555919413546837915324587505606808630079787225374099676477949367137087923900198389174875482753308873380888041895518676309555826689893728255
def reachable : Nat := 2246366308831963543654611451367930802891860213783763297936336069622087552124179839713950397968514252814549104877612669965711987293270260390606959112355840
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
theorem oddSide_length : oddSide.length = 50 := by decide
theorem evenSide_length : evenSide.length = 50 := by decide

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

end Snake9.Regrowth.E112228
