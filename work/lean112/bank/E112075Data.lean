import RegrowthParityCounts
namespace Snake9.Regrowth.E112075
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[81, 80, 82, 66, 67, 75, 73, 77, 76, 92, 94, 95, 87, 343, 341, 349, 345, 347, 346, 330, 334, 270, 286, 284, 280, 272, 274, 275, 259, 267, 265, 269, 261, 260, 324, 452, 453, 461, 457, 459, 451, 467, 466, 464, 472, 476, 478, 479, 415, 411, 409, 401, 405, 404, 406, 390, 386, 394, 392, 396, 140, 156, 152, 144, 146, 147, 151, 183, 247, 255, 254, 252, 248, 240, 242, 226, 227, 235, 233, 237, 229, 228, 164, 36, 37, 45, 41, 43, 35, 51, 50, 48, 56, 60, 62, 63, 319, 315, 313, 305, 309, 308, 310, 294, 290, 298, 296, 300, 364, 380, 376, 368]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (7 : Vertex), (8 : Vertex), (10 : Vertex), (15 : Vertex), (20 : Vertex), (21 : Vertex), (22 : Vertex), (25 : Vertex), (26 : Vertex), (27 : Vertex), (29 : Vertex), (96 : Vertex), (97 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (106 : Vertex), (110 : Vertex), (111 : Vertex), (116 : Vertex), (117 : Vertex), (118 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (125 : Vertex), (129 : Vertex), (133 : Vertex), (137 : Vertex), (139 : Vertex), (143 : Vertex), (161 : Vertex), (168 : Vertex), (170 : Vertex), (174 : Vertex), (175 : Vertex), (177 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (202 : Vertex), (206 : Vertex), (207 : Vertex), (212 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (321 : Vertex), (352 : Vertex), (353 : Vertex), (355 : Vertex), (357 : Vertex), (359 : Vertex), (361 : Vertex), (363 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (371 : Vertex), (416 : Vertex), (417 : Vertex), (419 : Vertex), (421 : Vertex), (423 : Vertex), (425 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (431 : Vertex), (432 : Vertex), (434 : Vertex), (435 : Vertex), (440 : Vertex), (442 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (490 : Vertex), (494 : Vertex), (495 : Vertex), (497 : Vertex), (500 : Vertex), (501 : Vertex), (502 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (509 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (7 : Vertex), (8 : Vertex), (21 : Vertex), (22 : Vertex), (25 : Vertex), (26 : Vertex), (97 : Vertex), (103 : Vertex), (104 : Vertex), (110 : Vertex), (117 : Vertex), (118 : Vertex), (121 : Vertex), (122 : Vertex), (133 : Vertex), (137 : Vertex), (143 : Vertex), (161 : Vertex), (168 : Vertex), (174 : Vertex), (185 : Vertex), (186 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (206 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (321 : Vertex), (352 : Vertex), (355 : Vertex), (357 : Vertex), (361 : Vertex), (367 : Vertex), (370 : Vertex), (416 : Vertex), (419 : Vertex), (421 : Vertex), (425 : Vertex), (431 : Vertex), (434 : Vertex), (440 : Vertex), (445 : Vertex), (446 : Vertex), (481 : Vertex), (487 : Vertex), (488 : Vertex), (494 : Vertex), (501 : Vertex), (502 : Vertex), (505 : Vertex), (506 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (10 : Vertex), (15 : Vertex), (20 : Vertex), (27 : Vertex), (29 : Vertex), (96 : Vertex), (102 : Vertex), (106 : Vertex), (111 : Vertex), (116 : Vertex), (123 : Vertex), (125 : Vertex), (129 : Vertex), (139 : Vertex), (170 : Vertex), (175 : Vertex), (177 : Vertex), (187 : Vertex), (189 : Vertex), (192 : Vertex), (198 : Vertex), (202 : Vertex), (207 : Vertex), (212 : Vertex), (219 : Vertex), (221 : Vertex), (353 : Vertex), (359 : Vertex), (363 : Vertex), (368 : Vertex), (371 : Vertex), (417 : Vertex), (423 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (432 : Vertex), (435 : Vertex), (442 : Vertex), (444 : Vertex), (480 : Vertex), (486 : Vertex), (490 : Vertex), (495 : Vertex), (497 : Vertex), (500 : Vertex), (507 : Vertex), (509 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (6 : Vertex), (7 : Vertex), (8 : Vertex), (10 : Vertex), (15 : Vertex), (20 : Vertex), (21 : Vertex), (22 : Vertex), (25 : Vertex), (26 : Vertex), (27 : Vertex), (29 : Vertex), (96 : Vertex), (97 : Vertex), (102 : Vertex), (103 : Vertex), (104 : Vertex), (106 : Vertex), (110 : Vertex), (111 : Vertex), (116 : Vertex), (117 : Vertex), (118 : Vertex), (121 : Vertex), (122 : Vertex), (123 : Vertex), (125 : Vertex), (129 : Vertex), (133 : Vertex), (137 : Vertex), (139 : Vertex), (143 : Vertex), (161 : Vertex), (168 : Vertex), (170 : Vertex), (174 : Vertex), (175 : Vertex), (177 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (192 : Vertex), (193 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (202 : Vertex), (206 : Vertex), (207 : Vertex), (212 : Vertex), (213 : Vertex), (214 : Vertex), (217 : Vertex), (218 : Vertex), (219 : Vertex), (221 : Vertex), (321 : Vertex), (352 : Vertex), (353 : Vertex), (355 : Vertex), (357 : Vertex), (359 : Vertex), (361 : Vertex), (363 : Vertex), (367 : Vertex), (370 : Vertex), (371 : Vertex), (416 : Vertex), (417 : Vertex), (419 : Vertex), (421 : Vertex), (423 : Vertex), (425 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (431 : Vertex), (432 : Vertex), (434 : Vertex), (435 : Vertex), (440 : Vertex), (442 : Vertex), (444 : Vertex), (445 : Vertex), (446 : Vertex), (480 : Vertex), (481 : Vertex), (486 : Vertex), (487 : Vertex), (488 : Vertex), (490 : Vertex), (494 : Vertex), (495 : Vertex), (497 : Vertex), (500 : Vertex), (501 : Vertex), (502 : Vertex), (505 : Vertex), (506 : Vertex), (507 : Vertex), (509 : Vertex)]
def head : Vertex := 368
def ban : Nat := 10975111489685919824349432892578607680797483300050733088911926509163725023628365278068797142690578252393223380258342961800178673326580395310308117487516220
def reachable : Nat := 2432696440256677275224592105627238446681882520541660288811634934558039006445181698733077155476325175296808477928143089053575209485366174636125531518567875
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

end Snake9.Regrowth.E112075
