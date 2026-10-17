import RegrowthParityCounts
namespace Snake9.Regrowth.E112074
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 8, 10, 26, 27, 25, 29, 21, 20, 22, 6, 7, 15, 143, 207, 199, 198, 214, 212, 213, 221, 217, 219, 218, 202, 200, 192, 193, 129, 161, 177, 185, 187, 186, 170, 174, 430, 446, 444, 445, 429, 425, 427, 419, 435, 434, 432, 416, 480, 488, 490, 506, 507, 505, 497, 501, 500, 502, 486, 487, 495, 367, 111, 103, 102, 118, 116, 117, 125, 121, 123, 122, 106, 104, 96, 97, 353, 355, 371, 370, 368, 376, 380, 364, 300, 296, 298, 290, 294, 310, 308, 309, 305, 313, 315, 319, 63, 62, 60, 56, 48, 50, 51, 35, 43, 41, 45, 37, 36, 164, 228, 229]
def region : List Vertex := [(66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (73 : Vertex), (75 : Vertex), (76 : Vertex), (77 : Vertex), (78 : Vertex), (80 : Vertex), (81 : Vertex), (82 : Vertex), (83 : Vertex), (87 : Vertex), (88 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (130 : Vertex), (140 : Vertex), (144 : Vertex), (146 : Vertex), (147 : Vertex), (151 : Vertex), (152 : Vertex), (156 : Vertex), (158 : Vertex), (167 : Vertex), (182 : Vertex), (183 : Vertex), (226 : Vertex), (227 : Vertex), (229 : Vertex), (233 : Vertex), (235 : Vertex), (237 : Vertex), (240 : Vertex), (242 : Vertex), (243 : Vertex), (247 : Vertex), (248 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (257 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (265 : Vertex), (267 : Vertex), (269 : Vertex), (270 : Vertex), (272 : Vertex), (274 : Vertex), (275 : Vertex), (279 : Vertex), (280 : Vertex), (284 : Vertex), (286 : Vertex), (320 : Vertex), (322 : Vertex), (324 : Vertex), (325 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (330 : Vertex), (331 : Vertex), (333 : Vertex), (334 : Vertex), (337 : Vertex), (340 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (349 : Vertex), (350 : Vertex), (351 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (394 : Vertex), (396 : Vertex), (401 : Vertex), (404 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (411 : Vertex), (415 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (457 : Vertex), (459 : Vertex), (460 : Vertex), (461 : Vertex), (462 : Vertex), (464 : Vertex), (466 : Vertex), (467 : Vertex), (471 : Vertex), (472 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(67 : Vertex), (69 : Vertex), (73 : Vertex), (76 : Vertex), (81 : Vertex), (82 : Vertex), (87 : Vertex), (88 : Vertex), (94 : Vertex), (140 : Vertex), (146 : Vertex), (151 : Vertex), (152 : Vertex), (158 : Vertex), (167 : Vertex), (182 : Vertex), (227 : Vertex), (229 : Vertex), (233 : Vertex), (242 : Vertex), (247 : Vertex), (248 : Vertex), (254 : Vertex), (259 : Vertex), (261 : Vertex), (265 : Vertex), (274 : Vertex), (279 : Vertex), (280 : Vertex), (286 : Vertex), (322 : Vertex), (324 : Vertex), (327 : Vertex), (328 : Vertex), (331 : Vertex), (333 : Vertex), (334 : Vertex), (341 : Vertex), (342 : Vertex), (345 : Vertex), (346 : Vertex), (351 : Vertex), (386 : Vertex), (388 : Vertex), (391 : Vertex), (392 : Vertex), (405 : Vertex), (406 : Vertex), (409 : Vertex), (410 : Vertex), (415 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex), (460 : Vertex), (466 : Vertex), (471 : Vertex), (472 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(66 : Vertex), (68 : Vertex), (75 : Vertex), (77 : Vertex), (78 : Vertex), (80 : Vertex), (83 : Vertex), (92 : Vertex), (95 : Vertex), (130 : Vertex), (144 : Vertex), (147 : Vertex), (156 : Vertex), (183 : Vertex), (226 : Vertex), (235 : Vertex), (237 : Vertex), (240 : Vertex), (243 : Vertex), (252 : Vertex), (255 : Vertex), (257 : Vertex), (260 : Vertex), (267 : Vertex), (269 : Vertex), (270 : Vertex), (272 : Vertex), (275 : Vertex), (284 : Vertex), (320 : Vertex), (325 : Vertex), (326 : Vertex), (329 : Vertex), (330 : Vertex), (337 : Vertex), (340 : Vertex), (343 : Vertex), (347 : Vertex), (349 : Vertex), (350 : Vertex), (389 : Vertex), (390 : Vertex), (394 : Vertex), (396 : Vertex), (401 : Vertex), (404 : Vertex), (407 : Vertex), (408 : Vertex), (411 : Vertex), (450 : Vertex), (452 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (476 : Vertex), (479 : Vertex)]
def others : List Vertex := [(66 : Vertex), (67 : Vertex), (68 : Vertex), (69 : Vertex), (73 : Vertex), (75 : Vertex), (76 : Vertex), (77 : Vertex), (78 : Vertex), (80 : Vertex), (81 : Vertex), (82 : Vertex), (83 : Vertex), (87 : Vertex), (88 : Vertex), (92 : Vertex), (94 : Vertex), (95 : Vertex), (130 : Vertex), (140 : Vertex), (144 : Vertex), (146 : Vertex), (147 : Vertex), (151 : Vertex), (152 : Vertex), (156 : Vertex), (158 : Vertex), (167 : Vertex), (182 : Vertex), (183 : Vertex), (226 : Vertex), (227 : Vertex), (233 : Vertex), (235 : Vertex), (237 : Vertex), (240 : Vertex), (242 : Vertex), (243 : Vertex), (247 : Vertex), (248 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (257 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (265 : Vertex), (267 : Vertex), (269 : Vertex), (270 : Vertex), (272 : Vertex), (274 : Vertex), (275 : Vertex), (279 : Vertex), (280 : Vertex), (284 : Vertex), (286 : Vertex), (320 : Vertex), (322 : Vertex), (324 : Vertex), (325 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (330 : Vertex), (331 : Vertex), (333 : Vertex), (334 : Vertex), (337 : Vertex), (340 : Vertex), (341 : Vertex), (342 : Vertex), (343 : Vertex), (345 : Vertex), (346 : Vertex), (347 : Vertex), (349 : Vertex), (350 : Vertex), (351 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (394 : Vertex), (396 : Vertex), (401 : Vertex), (404 : Vertex), (405 : Vertex), (406 : Vertex), (407 : Vertex), (408 : Vertex), (409 : Vertex), (410 : Vertex), (411 : Vertex), (415 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (457 : Vertex), (459 : Vertex), (460 : Vertex), (461 : Vertex), (462 : Vertex), (464 : Vertex), (466 : Vertex), (467 : Vertex), (471 : Vertex), (472 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex)]
def head : Vertex := 229
def ban : Nat := 13407807927387242919458652205390244106810766299189541817464374833133700433162976356723453744585853437238110097734799872050103578387412365738556761269338111
def reachable : Nat := 2555354180115372792815602020668599521402851560259186610588063596910570620078420553581049990451921760451686178803650304424534204207876887736745984
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
theorem evenSide_length : evenSide.length = 58 := by decide

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

end Snake9.Regrowth.E112074
