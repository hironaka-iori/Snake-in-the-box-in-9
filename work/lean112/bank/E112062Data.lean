import RegrowthParityCounts
namespace Snake9.Regrowth.E112062
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 1, 3, 7, 15, 13, 12, 28, 20, 22, 18, 26, 27, 155, 411, 410, 402, 406, 404, 412, 413, 397, 399, 391, 387, 385, 384, 392, 136, 138, 142, 134, 132, 133, 149, 145, 209, 193, 195, 194, 210, 214, 212, 220, 204, 205, 207, 223, 479, 471, 469, 453, 452, 454, 462, 458, 459, 457, 473, 472, 464, 336, 80, 88, 89, 73, 75, 74, 78, 70, 68, 69, 85, 87, 83, 339, 323, 327, 335, 333, 332, 328, 360, 296, 288, 289, 291, 295, 303, 301, 317, 316, 308, 310, 306, 314, 315, 379, 507, 506, 498, 502, 500, 508, 492, 493, 495, 487, 483, 481, 480, 224]
def region : List Vertex := [(34 : Vertex), (36 : Vertex), (37 : Vertex), (38 : Vertex), (41 : Vertex), (42 : Vertex), (43 : Vertex), (46 : Vertex), (48 : Vertex), (49 : Vertex), (51 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (62 : Vertex), (63 : Vertex), (96 : Vertex), (97 : Vertex), (98 : Vertex), (99 : Vertex), (103 : Vertex), (108 : Vertex), (109 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (116 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (127 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (163 : Vertex), (167 : Vertex), (169 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (191 : Vertex), (224 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (238 : Vertex), (240 : Vertex), (243 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (253 : Vertex), (254 : Vertex), (258 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (270 : Vertex), (273 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (286 : Vertex), (287 : Vertex), (342 : Vertex), (346 : Vertex), (350 : Vertex), (354 : Vertex), (356 : Vertex), (357 : Vertex), (358 : Vertex), (366 : Vertex), (369 : Vertex), (373 : Vertex), (375 : Vertex), (382 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (427 : Vertex), (430 : Vertex), (432 : Vertex), (433 : Vertex), (435 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (446 : Vertex), (447 : Vertex)]
def oddSide : List Vertex := [(37 : Vertex), (38 : Vertex), (41 : Vertex), (42 : Vertex), (49 : Vertex), (55 : Vertex), (56 : Vertex), (62 : Vertex), (97 : Vertex), (98 : Vertex), (103 : Vertex), (109 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (127 : Vertex), (161 : Vertex), (162 : Vertex), (167 : Vertex), (171 : Vertex), (173 : Vertex), (176 : Vertex), (179 : Vertex), (182 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (191 : Vertex), (224 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (234 : Vertex), (247 : Vertex), (248 : Vertex), (253 : Vertex), (254 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (273 : Vertex), (279 : Vertex), (280 : Vertex), (286 : Vertex), (342 : Vertex), (346 : Vertex), (357 : Vertex), (358 : Vertex), (369 : Vertex), (375 : Vertex), (382 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (433 : Vertex), (439 : Vertex), (440 : Vertex), (446 : Vertex)]
def evenSide : List Vertex := [(34 : Vertex), (36 : Vertex), (43 : Vertex), (46 : Vertex), (48 : Vertex), (51 : Vertex), (53 : Vertex), (57 : Vertex), (63 : Vertex), (96 : Vertex), (99 : Vertex), (108 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (116 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (163 : Vertex), (169 : Vertex), (172 : Vertex), (175 : Vertex), (178 : Vertex), (180 : Vertex), (183 : Vertex), (184 : Vertex), (189 : Vertex), (190 : Vertex), (228 : Vertex), (232 : Vertex), (235 : Vertex), (238 : Vertex), (240 : Vertex), (243 : Vertex), (245 : Vertex), (249 : Vertex), (258 : Vertex), (260 : Vertex), (267 : Vertex), (270 : Vertex), (277 : Vertex), (281 : Vertex), (287 : Vertex), (350 : Vertex), (354 : Vertex), (356 : Vertex), (366 : Vertex), (373 : Vertex), (418 : Vertex), (420 : Vertex), (427 : Vertex), (430 : Vertex), (432 : Vertex), (435 : Vertex), (437 : Vertex), (441 : Vertex), (447 : Vertex)]
def others : List Vertex := [(34 : Vertex), (36 : Vertex), (37 : Vertex), (38 : Vertex), (41 : Vertex), (42 : Vertex), (43 : Vertex), (46 : Vertex), (48 : Vertex), (49 : Vertex), (51 : Vertex), (53 : Vertex), (55 : Vertex), (56 : Vertex), (57 : Vertex), (62 : Vertex), (63 : Vertex), (96 : Vertex), (97 : Vertex), (98 : Vertex), (99 : Vertex), (103 : Vertex), (108 : Vertex), (109 : Vertex), (111 : Vertex), (113 : Vertex), (114 : Vertex), (116 : Vertex), (118 : Vertex), (122 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (127 : Vertex), (160 : Vertex), (161 : Vertex), (162 : Vertex), (163 : Vertex), (167 : Vertex), (169 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (175 : Vertex), (176 : Vertex), (178 : Vertex), (179 : Vertex), (180 : Vertex), (182 : Vertex), (183 : Vertex), (184 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (191 : Vertex), (228 : Vertex), (229 : Vertex), (230 : Vertex), (232 : Vertex), (233 : Vertex), (234 : Vertex), (235 : Vertex), (238 : Vertex), (240 : Vertex), (243 : Vertex), (245 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (253 : Vertex), (254 : Vertex), (258 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (266 : Vertex), (267 : Vertex), (270 : Vertex), (273 : Vertex), (277 : Vertex), (279 : Vertex), (280 : Vertex), (281 : Vertex), (286 : Vertex), (287 : Vertex), (342 : Vertex), (346 : Vertex), (350 : Vertex), (354 : Vertex), (356 : Vertex), (357 : Vertex), (358 : Vertex), (366 : Vertex), (369 : Vertex), (373 : Vertex), (375 : Vertex), (382 : Vertex), (418 : Vertex), (420 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (426 : Vertex), (427 : Vertex), (430 : Vertex), (432 : Vertex), (433 : Vertex), (435 : Vertex), (437 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (446 : Vertex), (447 : Vertex)]
def head : Vertex := 224
def ban : Nat := 13407807929942597099018478408791115420006515883651938770025916082572339018372999059240717384889664032547715408740845959128890453800750234476869680357179391
def reachable : Nat := 555546589414730707472849936940454607697645361149425011700547917561156913277239395142316449445640091724863429011196335469563968648904704
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
theorem oddSide_length : oddSide.length = 60 := by decide
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

end Snake9.Regrowth.E112062
