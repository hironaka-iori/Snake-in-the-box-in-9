import RegrowthParityCounts
namespace Snake9.Regrowth.E112147
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[11, 10, 26, 24, 25, 29, 13, 77, 333, 332, 324, 326, 342, 343, 351, 95, 94, 92, 84, 80, 81, 337, 345, 344, 346, 330, 331, 323, 67, 195, 203, 202, 218, 216, 217, 221, 213, 215, 214, 198, 196, 204, 140, 156, 158, 159, 143, 135, 133, 129, 145, 144, 146, 130, 386, 390, 406, 407, 405, 413, 397, 429, 493, 492, 484, 486, 502, 503, 501, 497, 505, 504, 506, 490, 491, 483, 419, 291, 299, 298, 314, 312, 313, 317, 309, 311, 310, 294, 292, 300, 44, 60, 62, 63, 47, 39, 37, 33, 49, 48, 50, 34, 98, 102, 118, 119, 117, 125, 121, 123, 379, 371]
def region : List Vertex := [(0 : Vertex), (4 : Vertex), (6 : Vertex), (19 : Vertex), (22 : Vertex), (23 : Vertex), (72 : Vertex), (104 : Vertex), (160 : Vertex), (164 : Vertex), (166 : Vertex), (168 : Vertex), (169 : Vertex), (170 : Vertex), (171 : Vertex), (174 : Vertex), (179 : Vertex), (180 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (224 : Vertex), (225 : Vertex), (229 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (238 : Vertex), (239 : Vertex), (240 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (256 : Vertex), (257 : Vertex), (261 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (270 : Vertex), (271 : Vertex), (272 : Vertex), (274 : Vertex), (275 : Vertex), (276 : Vertex), (283 : Vertex), (284 : Vertex), (286 : Vertex), (352 : Vertex), (353 : Vertex), (357 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (366 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (371 : Vertex), (372 : Vertex), (380 : Vertex), (382 : Vertex), (392 : Vertex), (395 : Vertex), (408 : Vertex), (410 : Vertex), (411 : Vertex), (416 : Vertex), (424 : Vertex), (430 : Vertex), (432 : Vertex), (434 : Vertex), (436 : Vertex), (443 : Vertex), (444 : Vertex), (446 : Vertex), (447 : Vertex), (448 : Vertex), (449 : Vertex), (453 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (475 : Vertex), (476 : Vertex), (478 : Vertex)]
def oddSide : List Vertex := [(4 : Vertex), (19 : Vertex), (22 : Vertex), (104 : Vertex), (164 : Vertex), (168 : Vertex), (171 : Vertex), (174 : Vertex), (179 : Vertex), (181 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (224 : Vertex), (229 : Vertex), (233 : Vertex), (239 : Vertex), (242 : Vertex), (244 : Vertex), (254 : Vertex), (256 : Vertex), (261 : Vertex), (265 : Vertex), (271 : Vertex), (274 : Vertex), (276 : Vertex), (283 : Vertex), (286 : Vertex), (352 : Vertex), (357 : Vertex), (361 : Vertex), (367 : Vertex), (370 : Vertex), (372 : Vertex), (382 : Vertex), (392 : Vertex), (395 : Vertex), (410 : Vertex), (416 : Vertex), (434 : Vertex), (436 : Vertex), (443 : Vertex), (446 : Vertex), (448 : Vertex), (453 : Vertex), (457 : Vertex), (463 : Vertex), (466 : Vertex), (468 : Vertex), (475 : Vertex), (478 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (23 : Vertex), (72 : Vertex), (160 : Vertex), (166 : Vertex), (169 : Vertex), (170 : Vertex), (180 : Vertex), (183 : Vertex), (184 : Vertex), (187 : Vertex), (189 : Vertex), (225 : Vertex), (231 : Vertex), (232 : Vertex), (238 : Vertex), (240 : Vertex), (243 : Vertex), (252 : Vertex), (255 : Vertex), (257 : Vertex), (263 : Vertex), (264 : Vertex), (270 : Vertex), (272 : Vertex), (275 : Vertex), (284 : Vertex), (353 : Vertex), (359 : Vertex), (360 : Vertex), (366 : Vertex), (368 : Vertex), (371 : Vertex), (380 : Vertex), (408 : Vertex), (411 : Vertex), (424 : Vertex), (430 : Vertex), (432 : Vertex), (444 : Vertex), (447 : Vertex), (449 : Vertex), (455 : Vertex), (456 : Vertex), (462 : Vertex), (464 : Vertex), (467 : Vertex), (476 : Vertex)]
def others : List Vertex := [(0 : Vertex), (4 : Vertex), (6 : Vertex), (19 : Vertex), (22 : Vertex), (23 : Vertex), (72 : Vertex), (104 : Vertex), (160 : Vertex), (164 : Vertex), (166 : Vertex), (168 : Vertex), (169 : Vertex), (170 : Vertex), (171 : Vertex), (174 : Vertex), (179 : Vertex), (180 : Vertex), (181 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (187 : Vertex), (189 : Vertex), (224 : Vertex), (225 : Vertex), (229 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (238 : Vertex), (239 : Vertex), (240 : Vertex), (242 : Vertex), (243 : Vertex), (244 : Vertex), (252 : Vertex), (254 : Vertex), (255 : Vertex), (256 : Vertex), (257 : Vertex), (261 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (270 : Vertex), (271 : Vertex), (272 : Vertex), (274 : Vertex), (275 : Vertex), (276 : Vertex), (283 : Vertex), (284 : Vertex), (286 : Vertex), (352 : Vertex), (353 : Vertex), (357 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (366 : Vertex), (367 : Vertex), (368 : Vertex), (370 : Vertex), (372 : Vertex), (380 : Vertex), (382 : Vertex), (392 : Vertex), (395 : Vertex), (408 : Vertex), (410 : Vertex), (411 : Vertex), (416 : Vertex), (424 : Vertex), (430 : Vertex), (432 : Vertex), (434 : Vertex), (436 : Vertex), (443 : Vertex), (444 : Vertex), (446 : Vertex), (447 : Vertex), (448 : Vertex), (449 : Vertex), (453 : Vertex), (455 : Vertex), (456 : Vertex), (457 : Vertex), (462 : Vertex), (463 : Vertex), (464 : Vertex), (466 : Vertex), (467 : Vertex), (468 : Vertex), (475 : Vertex), (476 : Vertex), (478 : Vertex)]
def head : Vertex := 371
def ban : Nat := 13407807928868078243549140207837123823685642077573194182228644129679442198502513283821420111731493167732584802635963196431015016820916577836492834983116718
def reachable : Nat := 1074518856024884790368722303793723743019199195494917314042321831571033692980454186435410259957447055550522854422738865991029992109940814022967377
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
theorem oddSide_length : oddSide.length = 51 := by decide
theorem evenSide_length : evenSide.length = 49 := by decide

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

end Snake9.Regrowth.E112147
