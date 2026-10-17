import RegrowthParityCounts
namespace Snake9.Regrowth.E112163
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[13, 12, 28, 30, 31, 27, 19, 17, 21, 85, 84, 86, 82, 90, 88, 89, 73, 65, 67, 71, 79, 78, 206, 462, 463, 455, 451, 449, 457, 456, 472, 474, 466, 470, 468, 469, 477, 221, 223, 219, 211, 209, 208, 192, 196, 132, 148, 150, 151, 135, 131, 129, 137, 153, 152, 154, 138, 394, 386, 384, 400, 401, 403, 411, 415, 414, 412, 396, 397, 389, 261, 325, 333, 332, 348, 350, 351, 343, 339, 337, 336, 320, 322, 330, 331, 267, 299, 315, 307, 305, 304, 288, 292, 36, 52, 54, 55, 39, 35, 33, 41, 57, 56, 58, 42, 106, 98, 96, 112, 113, 115, 123]
def region : List Vertex := [(0 : Vertex), (2 : Vertex), (6 : Vertex), (101 : Vertex), (108 : Vertex), (109 : Vertex), (123 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (127 : Vertex), (160 : Vertex), (162 : Vertex), (165 : Vertex), (166 : Vertex), (168 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (174 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (181 : Vertex), (187 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (191 : Vertex), (225 : Vertex), (227 : Vertex), (229 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (235 : Vertex), (236 : Vertex), (237 : Vertex), (239 : Vertex), (242 : Vertex), (244 : Vertex), (245 : Vertex), (246 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (250 : Vertex), (252 : Vertex), (254 : Vertex), (262 : Vertex), (264 : Vertex), (270 : Vertex), (274 : Vertex), (276 : Vertex), (278 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (285 : Vertex), (301 : Vertex), (302 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (353 : Vertex), (355 : Vertex), (358 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (366 : Vertex), (367 : Vertex), (370 : Vertex), (372 : Vertex), (373 : Vertex), (374 : Vertex), (376 : Vertex), (377 : Vertex), (378 : Vertex), (381 : Vertex), (417 : Vertex), (419 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (430 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (437 : Vertex), (438 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (445 : Vertex), (480 : Vertex), (482 : Vertex), (484 : Vertex), (485 : Vertex), (486 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (496 : Vertex), (497 : Vertex), (499 : Vertex), (503 : Vertex), (505 : Vertex), (507 : Vertex), (508 : Vertex), (510 : Vertex), (511 : Vertex)]
def oddSide : List Vertex := [(2 : Vertex), (109 : Vertex), (124 : Vertex), (127 : Vertex), (162 : Vertex), (168 : Vertex), (171 : Vertex), (173 : Vertex), (174 : Vertex), (176 : Vertex), (179 : Vertex), (181 : Vertex), (188 : Vertex), (191 : Vertex), (227 : Vertex), (229 : Vertex), (230 : Vertex), (233 : Vertex), (236 : Vertex), (239 : Vertex), (242 : Vertex), (244 : Vertex), (247 : Vertex), (248 : Vertex), (254 : Vertex), (262 : Vertex), (274 : Vertex), (276 : Vertex), (280 : Vertex), (285 : Vertex), (301 : Vertex), (302 : Vertex), (316 : Vertex), (355 : Vertex), (358 : Vertex), (361 : Vertex), (367 : Vertex), (370 : Vertex), (372 : Vertex), (376 : Vertex), (381 : Vertex), (419 : Vertex), (422 : Vertex), (425 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (439 : Vertex), (440 : Vertex), (445 : Vertex), (482 : Vertex), (484 : Vertex), (491 : Vertex), (493 : Vertex), (496 : Vertex), (499 : Vertex), (505 : Vertex), (508 : Vertex), (511 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (101 : Vertex), (108 : Vertex), (123 : Vertex), (125 : Vertex), (126 : Vertex), (160 : Vertex), (165 : Vertex), (166 : Vertex), (172 : Vertex), (175 : Vertex), (177 : Vertex), (178 : Vertex), (187 : Vertex), (189 : Vertex), (190 : Vertex), (225 : Vertex), (231 : Vertex), (232 : Vertex), (235 : Vertex), (237 : Vertex), (245 : Vertex), (246 : Vertex), (249 : Vertex), (250 : Vertex), (252 : Vertex), (264 : Vertex), (270 : Vertex), (278 : Vertex), (281 : Vertex), (282 : Vertex), (317 : Vertex), (318 : Vertex), (353 : Vertex), (359 : Vertex), (360 : Vertex), (366 : Vertex), (373 : Vertex), (374 : Vertex), (377 : Vertex), (378 : Vertex), (417 : Vertex), (423 : Vertex), (424 : Vertex), (430 : Vertex), (437 : Vertex), (438 : Vertex), (441 : Vertex), (442 : Vertex), (480 : Vertex), (485 : Vertex), (486 : Vertex), (490 : Vertex), (492 : Vertex), (497 : Vertex), (503 : Vertex), (507 : Vertex), (510 : Vertex)]
def others : List Vertex := [(0 : Vertex), (2 : Vertex), (6 : Vertex), (101 : Vertex), (108 : Vertex), (109 : Vertex), (124 : Vertex), (125 : Vertex), (126 : Vertex), (127 : Vertex), (160 : Vertex), (162 : Vertex), (165 : Vertex), (166 : Vertex), (168 : Vertex), (171 : Vertex), (172 : Vertex), (173 : Vertex), (174 : Vertex), (175 : Vertex), (176 : Vertex), (177 : Vertex), (178 : Vertex), (179 : Vertex), (181 : Vertex), (187 : Vertex), (188 : Vertex), (189 : Vertex), (190 : Vertex), (191 : Vertex), (225 : Vertex), (227 : Vertex), (229 : Vertex), (230 : Vertex), (231 : Vertex), (232 : Vertex), (233 : Vertex), (235 : Vertex), (236 : Vertex), (237 : Vertex), (239 : Vertex), (242 : Vertex), (244 : Vertex), (245 : Vertex), (246 : Vertex), (247 : Vertex), (248 : Vertex), (249 : Vertex), (250 : Vertex), (252 : Vertex), (254 : Vertex), (262 : Vertex), (264 : Vertex), (270 : Vertex), (274 : Vertex), (276 : Vertex), (278 : Vertex), (280 : Vertex), (281 : Vertex), (282 : Vertex), (285 : Vertex), (301 : Vertex), (302 : Vertex), (316 : Vertex), (317 : Vertex), (318 : Vertex), (353 : Vertex), (355 : Vertex), (358 : Vertex), (359 : Vertex), (360 : Vertex), (361 : Vertex), (366 : Vertex), (367 : Vertex), (370 : Vertex), (372 : Vertex), (373 : Vertex), (374 : Vertex), (376 : Vertex), (377 : Vertex), (378 : Vertex), (381 : Vertex), (417 : Vertex), (419 : Vertex), (422 : Vertex), (423 : Vertex), (424 : Vertex), (425 : Vertex), (430 : Vertex), (431 : Vertex), (434 : Vertex), (436 : Vertex), (437 : Vertex), (438 : Vertex), (439 : Vertex), (440 : Vertex), (441 : Vertex), (442 : Vertex), (445 : Vertex), (480 : Vertex), (482 : Vertex), (484 : Vertex), (485 : Vertex), (486 : Vertex), (490 : Vertex), (491 : Vertex), (492 : Vertex), (493 : Vertex), (496 : Vertex), (497 : Vertex), (499 : Vertex), (503 : Vertex), (505 : Vertex), (507 : Vertex), (508 : Vertex), (510 : Vertex), (511 : Vertex)]
def head : Vertex := 123
def ban : Nat := 1961735593392443283747070712511293698097666455560936134652474010329571828345950862782146194856090024058970235666962575208690615391726350408071135130288058
def reachable : Nat := 11446072336550153815826954285694552429381699365031457243071087433392192201727596114019728103310813403631061622519523475645063267420220219538362513875796037
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

end Snake9.Regrowth.E112163
