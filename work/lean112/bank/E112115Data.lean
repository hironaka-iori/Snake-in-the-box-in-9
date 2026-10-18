import RegrowthParityCounts
namespace Snake9.Regrowth.E112115
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[342, 350, 348, 332, 333, 335, 331, 323, 322, 320, 336, 337, 345, 473, 409, 401, 400, 384, 386, 387, 395, 399, 397, 396, 412, 414, 406, 407, 471, 503, 487, 495, 493, 492, 508, 504, 248, 232, 234, 235, 251, 255, 253, 245, 229, 228, 230, 246, 182, 190, 188, 172, 173, 175, 167, 163, 162, 160, 176, 177, 185, 57, 313, 305, 304, 288, 290, 291, 299, 303, 301, 300, 316, 318, 310, 311, 55, 53, 37, 36, 38, 46, 42, 58, 122, 126, 124, 116, 112, 96, 98, 99, 103, 111, 109, 105, 361, 360, 362, 366, 358, 356, 357, 373, 381, 383, 379, 371, 370, 498, 434, 435]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (2 : Vertex), (3 : Vertex), (7 : Vertex), (8 : Vertex), (9 : Vertex), (11 : Vertex), (12 : Vertex), (13 : Vertex), (15 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (20 : Vertex), (22 : Vertex), (24 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (31 : Vertex), (65 : Vertex), (68 : Vertex), (69 : Vertex), (70 : Vertex), (72 : Vertex), (74 : Vertex), (78 : Vertex), (82 : Vertex), (83 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (91 : Vertex), (93 : Vertex), (95 : Vertex), (129 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (142 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (152 : Vertex), (154 : Vertex), (155 : Vertex), (157 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (199 : Vertex), (201 : Vertex), (204 : Vertex), (205 : Vertex), (206 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (212 : Vertex), (218 : Vertex), (220 : Vertex), (222 : Vertex), (257 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (270 : Vertex), (274 : Vertex), (275 : Vertex), (276 : Vertex), (277 : Vertex), (280 : Vertex), (282 : Vertex), (283 : Vertex), (285 : Vertex), (287 : Vertex), (417 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (424 : Vertex), (425 : Vertex), (426 : Vertex), (430 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (443 : Vertex), (445 : Vertex), (447 : Vertex), (449 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (456 : Vertex), (458 : Vertex), (462 : Vertex), (468 : Vertex), (474 : Vertex), (480 : Vertex), (481 : Vertex), (497 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (2 : Vertex), (7 : Vertex), (8 : Vertex), (11 : Vertex), (13 : Vertex), (16 : Vertex), (19 : Vertex), (22 : Vertex), (28 : Vertex), (31 : Vertex), (69 : Vertex), (70 : Vertex), (74 : Vertex), (82 : Vertex), (87 : Vertex), (88 : Vertex), (91 : Vertex), (93 : Vertex), (133 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (146 : Vertex), (148 : Vertex), (152 : Vertex), (155 : Vertex), (157 : Vertex), (193 : Vertex), (194 : Vertex), (199 : Vertex), (205 : Vertex), (206 : Vertex), (208 : Vertex), (211 : Vertex), (218 : Vertex), (220 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (274 : Vertex), (276 : Vertex), (280 : Vertex), (283 : Vertex), (285 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (436 : Vertex), (443 : Vertex), (445 : Vertex), (453 : Vertex), (454 : Vertex), (458 : Vertex), (468 : Vertex), (481 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (3 : Vertex), (9 : Vertex), (12 : Vertex), (15 : Vertex), (17 : Vertex), (18 : Vertex), (20 : Vertex), (24 : Vertex), (27 : Vertex), (29 : Vertex), (30 : Vertex), (65 : Vertex), (68 : Vertex), (72 : Vertex), (78 : Vertex), (83 : Vertex), (85 : Vertex), (95 : Vertex), (129 : Vertex), (132 : Vertex), (136 : Vertex), (142 : Vertex), (147 : Vertex), (149 : Vertex), (154 : Vertex), (159 : Vertex), (192 : Vertex), (195 : Vertex), (201 : Vertex), (204 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex), (222 : Vertex), (257 : Vertex), (260 : Vertex), (263 : Vertex), (264 : Vertex), (270 : Vertex), (275 : Vertex), (277 : Vertex), (282 : Vertex), (287 : Vertex), (417 : Vertex), (420 : Vertex), (424 : Vertex), (430 : Vertex), (435 : Vertex), (437 : Vertex), (447 : Vertex), (449 : Vertex), (452 : Vertex), (456 : Vertex), (462 : Vertex), (474 : Vertex), (480 : Vertex), (497 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (2 : Vertex), (3 : Vertex), (7 : Vertex), (8 : Vertex), (9 : Vertex), (11 : Vertex), (12 : Vertex), (13 : Vertex), (15 : Vertex), (16 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (20 : Vertex), (22 : Vertex), (24 : Vertex), (27 : Vertex), (28 : Vertex), (29 : Vertex), (30 : Vertex), (31 : Vertex), (65 : Vertex), (68 : Vertex), (69 : Vertex), (70 : Vertex), (72 : Vertex), (74 : Vertex), (78 : Vertex), (82 : Vertex), (83 : Vertex), (85 : Vertex), (87 : Vertex), (88 : Vertex), (91 : Vertex), (93 : Vertex), (95 : Vertex), (129 : Vertex), (132 : Vertex), (133 : Vertex), (134 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (142 : Vertex), (146 : Vertex), (147 : Vertex), (148 : Vertex), (149 : Vertex), (152 : Vertex), (154 : Vertex), (155 : Vertex), (157 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (194 : Vertex), (195 : Vertex), (199 : Vertex), (201 : Vertex), (204 : Vertex), (205 : Vertex), (206 : Vertex), (207 : Vertex), (208 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (212 : Vertex), (218 : Vertex), (220 : Vertex), (222 : Vertex), (257 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (266 : Vertex), (270 : Vertex), (274 : Vertex), (275 : Vertex), (276 : Vertex), (277 : Vertex), (280 : Vertex), (282 : Vertex), (283 : Vertex), (285 : Vertex), (287 : Vertex), (417 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (424 : Vertex), (425 : Vertex), (426 : Vertex), (430 : Vertex), (436 : Vertex), (437 : Vertex), (443 : Vertex), (445 : Vertex), (447 : Vertex), (449 : Vertex), (452 : Vertex), (453 : Vertex), (454 : Vertex), (456 : Vertex), (458 : Vertex), (462 : Vertex), (468 : Vertex), (474 : Vertex), (480 : Vertex), (481 : Vertex), (497 : Vertex)]
def head : Vertex := 435
def ban : Nat := 13407398746701812041935078398520486171020852233310505246668777576108849463096585446423554980806613602154006618153941744522115416254546100116822489095488624
def reachable : Nat := 409183240785057638946599685359956458513587281888131054783867612914566976961530378319317360289825536025240032544306331638466557400469829611159910595471
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

end Snake9.Regrowth.E112115
