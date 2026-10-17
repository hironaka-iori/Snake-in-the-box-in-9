import RegrowthParityCounts
namespace Snake9.Regrowth.E112092
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 8, 12, 14, 6, 22, 23, 21, 29, 25, 27, 11, 75, 79, 95, 94, 92, 84, 340, 341, 343, 327, 326, 334, 332, 328, 329, 345, 347, 346, 338, 82, 83, 81, 65, 193, 192, 200, 204, 206, 198, 214, 215, 213, 221, 217, 219, 218, 154, 158, 156, 148, 144, 145, 147, 131, 135, 143, 141, 137, 393, 409, 413, 405, 407, 406, 402, 434, 498, 506, 507, 505, 509, 501, 503, 487, 486, 494, 492, 488, 480, 481, 417, 289, 288, 296, 300, 302, 294, 310, 311, 309, 317, 313, 315, 314, 58, 62, 60, 52, 48, 49, 51, 35, 39, 47, 45, 41, 105, 121, 125, 117]
def region : List Vertex := [(96 : Vertex), (98 : Vertex), (100 : Vertex), (101 : Vertex), (102 : Vertex), (106 : Vertex), (108 : Vertex), (110 : Vertex), (117 : Vertex), (118 : Vertex), (119 : Vertex), (160 : Vertex), (162 : Vertex), (164 : Vertex), (165 : Vertex), (166 : Vertex), (168 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (174 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (187 : Vertex), (189 : Vertex), (191 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (239 : Vertex), (240 : Vertex), (241 : Vertex), (243 : Vertex), (244 : Vertex), (248 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (266 : Vertex), (269 : Vertex), (271 : Vertex), (272 : Vertex), (273 : Vertex), (275 : Vertex), (280 : Vertex), (284 : Vertex), (286 : Vertex), (287 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (362 : Vertex), (363 : Vertex), (365 : Vertex), (367 : Vertex), (368 : Vertex), (369 : Vertex), (371 : Vertex), (376 : Vertex), (380 : Vertex), (382 : Vertex), (383 : Vertex), (384 : Vertex), (388 : Vertex), (394 : Vertex), (396 : Vertex), (398 : Vertex), (420 : Vertex), (426 : Vertex), (427 : Vertex), (429 : Vertex), (431 : Vertex), (436 : Vertex), (440 : Vertex), (444 : Vertex), (446 : Vertex), (447 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (458 : Vertex), (459 : Vertex), (461 : Vertex), (463 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (472 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(98 : Vertex), (100 : Vertex), (110 : Vertex), (117 : Vertex), (118 : Vertex), (162 : Vertex), (164 : Vertex), (168 : Vertex), (171 : Vertex), (174 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (191 : Vertex), (227 : Vertex), (229 : Vertex), (234 : Vertex), (239 : Vertex), (241 : Vertex), (244 : Vertex), (248 : Vertex), (254 : Vertex), (259 : Vertex), (261 : Vertex), (266 : Vertex), (271 : Vertex), (273 : Vertex), (280 : Vertex), (286 : Vertex), (355 : Vertex), (357 : Vertex), (362 : Vertex), (367 : Vertex), (369 : Vertex), (376 : Vertex), (382 : Vertex), (388 : Vertex), (398 : Vertex), (426 : Vertex), (431 : Vertex), (436 : Vertex), (440 : Vertex), (446 : Vertex), (451 : Vertex), (453 : Vertex), (458 : Vertex), (463 : Vertex), (465 : Vertex), (472 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(96 : Vertex), (101 : Vertex), (102 : Vertex), (106 : Vertex), (108 : Vertex), (119 : Vertex), (160 : Vertex), (165 : Vertex), (166 : Vertex), (170 : Vertex), (172 : Vertex), (183 : Vertex), (184 : Vertex), (187 : Vertex), (189 : Vertex), (226 : Vertex), (228 : Vertex), (235 : Vertex), (237 : Vertex), (240 : Vertex), (243 : Vertex), (252 : Vertex), (255 : Vertex), (258 : Vertex), (260 : Vertex), (269 : Vertex), (272 : Vertex), (275 : Vertex), (284 : Vertex), (287 : Vertex), (354 : Vertex), (356 : Vertex), (363 : Vertex), (365 : Vertex), (368 : Vertex), (371 : Vertex), (380 : Vertex), (383 : Vertex), (384 : Vertex), (394 : Vertex), (396 : Vertex), (420 : Vertex), (427 : Vertex), (429 : Vertex), (444 : Vertex), (447 : Vertex), (450 : Vertex), (452 : Vertex), (459 : Vertex), (461 : Vertex), (464 : Vertex), (467 : Vertex), (476 : Vertex), (479 : Vertex)]
def others : List Vertex := [(96 : Vertex), (98 : Vertex), (100 : Vertex), (101 : Vertex), (102 : Vertex), (106 : Vertex), (108 : Vertex), (110 : Vertex), (118 : Vertex), (119 : Vertex), (160 : Vertex), (162 : Vertex), (164 : Vertex), (165 : Vertex), (166 : Vertex), (168 : Vertex), (170 : Vertex), (171 : Vertex), (172 : Vertex), (174 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (187 : Vertex), (189 : Vertex), (191 : Vertex), (226 : Vertex), (227 : Vertex), (228 : Vertex), (229 : Vertex), (234 : Vertex), (235 : Vertex), (237 : Vertex), (239 : Vertex), (240 : Vertex), (241 : Vertex), (243 : Vertex), (244 : Vertex), (248 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (266 : Vertex), (269 : Vertex), (271 : Vertex), (272 : Vertex), (273 : Vertex), (275 : Vertex), (280 : Vertex), (284 : Vertex), (286 : Vertex), (287 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (357 : Vertex), (362 : Vertex), (363 : Vertex), (365 : Vertex), (367 : Vertex), (368 : Vertex), (369 : Vertex), (371 : Vertex), (376 : Vertex), (380 : Vertex), (382 : Vertex), (383 : Vertex), (384 : Vertex), (388 : Vertex), (394 : Vertex), (396 : Vertex), (398 : Vertex), (420 : Vertex), (426 : Vertex), (427 : Vertex), (429 : Vertex), (431 : Vertex), (436 : Vertex), (440 : Vertex), (444 : Vertex), (446 : Vertex), (447 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (458 : Vertex), (459 : Vertex), (461 : Vertex), (463 : Vertex), (464 : Vertex), (465 : Vertex), (467 : Vertex), (472 : Vertex), (476 : Vertex), (478 : Vertex), (479 : Vertex)]
def head : Vertex := 117
def ban : Nat := 13407807927393426048672007435455603376976299310918045152641978479536619436657019911017471401919762412123961257520810638057117606055310576775756888888311807
def reachable : Nat := 2549171050902017562750242750503066509674348225081582964185144593416527065784402896247141015566070600665675412796636276756635993170676760117772288
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

end Snake9.Regrowth.E112092
