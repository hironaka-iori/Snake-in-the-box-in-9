import RegrowthParityCounts
namespace Snake9.Regrowth.E112254
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 4, 36, 38, 166, 162, 178, 50, 18, 22, 150, 158, 142, 14, 10, 42, 40, 168, 172, 188, 60, 28, 24, 152, 144, 145, 17, 21, 53, 55, 183, 191, 175, 47, 45, 13, 141, 133, 165, 161, 33, 35, 3, 131, 139, 155, 27, 59, 57, 185, 249, 241, 113, 115, 83, 87, 215, 223, 207, 79, 75, 107, 235, 227, 231, 103, 101, 69, 65, 193, 201, 200, 72, 76, 108, 110, 238, 254, 246, 118, 116, 84, 212, 196, 228, 224, 96, 98, 66, 194, 210, 218, 90, 94, 350, 334, 330, 458, 459, 475, 467, 465, 469, 341, 373, 375, 503, 511, 495, 367, 365, 333]
def region : List Vertex := [(89 : Vertex), (93 : Vertex), (120 : Vertex), (125 : Vertex), (127 : Vertex), (257 : Vertex), (258 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (267 : Vertex), (268 : Vertex), (271 : Vertex), (272 : Vertex), (275 : Vertex), (276 : Vertex), (279 : Vertex), (281 : Vertex), (282 : Vertex), (285 : Vertex), (287 : Vertex), (288 : Vertex), (290 : Vertex), (293 : Vertex), (295 : Vertex), (297 : Vertex), (299 : Vertex), (300 : Vertex), (302 : Vertex), (304 : Vertex), (305 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (312 : Vertex), (314 : Vertex), (317 : Vertex), (318 : Vertex), (319 : Vertex), (320 : Vertex), (323 : Vertex), (324 : Vertex), (327 : Vertex), (329 : Vertex), (333 : Vertex), (336 : Vertex), (338 : Vertex), (344 : Vertex), (345 : Vertex), (353 : Vertex), (355 : Vertex), (356 : Vertex), (358 : Vertex), (360 : Vertex), (368 : Vertex), (370 : Vertex), (376 : Vertex), (377 : Vertex), (378 : Vertex), (379 : Vertex), (380 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (388 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex), (402 : Vertex), (404 : Vertex), (407 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (415 : Vertex), (416 : Vertex), (419 : Vertex), (420 : Vertex), (423 : Vertex), (425 : Vertex), (426 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (432 : Vertex), (433 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (438 : Vertex), (440 : Vertex), (442 : Vertex), (443 : Vertex), (445 : Vertex), (446 : Vertex), (448 : Vertex), (454 : Vertex), (455 : Vertex), (460 : Vertex), (461 : Vertex), (470 : Vertex), (472 : Vertex), (476 : Vertex), (481 : Vertex), (482 : Vertex), (485 : Vertex), (486 : Vertex), (488 : Vertex), (489 : Vertex), (492 : Vertex), (496 : Vertex), (498 : Vertex), (500 : Vertex), (504 : Vertex), (506 : Vertex), (508 : Vertex)]
def oddSide : List Vertex := [(93 : Vertex), (127 : Vertex), (261 : Vertex), (262 : Vertex), (265 : Vertex), (268 : Vertex), (271 : Vertex), (276 : Vertex), (279 : Vertex), (285 : Vertex), (290 : Vertex), (295 : Vertex), (299 : Vertex), (302 : Vertex), (304 : Vertex), (307 : Vertex), (310 : Vertex), (314 : Vertex), (319 : Vertex), (324 : Vertex), (327 : Vertex), (333 : Vertex), (336 : Vertex), (345 : Vertex), (355 : Vertex), (358 : Vertex), (370 : Vertex), (376 : Vertex), (379 : Vertex), (385 : Vertex), (386 : Vertex), (388 : Vertex), (391 : Vertex), (392 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (415 : Vertex), (416 : Vertex), (419 : Vertex), (425 : Vertex), (426 : Vertex), (433 : Vertex), (436 : Vertex), (440 : Vertex), (443 : Vertex), (445 : Vertex), (446 : Vertex), (448 : Vertex), (454 : Vertex), (460 : Vertex), (472 : Vertex), (481 : Vertex), (482 : Vertex), (488 : Vertex), (496 : Vertex), (506 : Vertex), (508 : Vertex)]
def evenSide : List Vertex := [(89 : Vertex), (120 : Vertex), (125 : Vertex), (257 : Vertex), (258 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (272 : Vertex), (275 : Vertex), (281 : Vertex), (282 : Vertex), (287 : Vertex), (288 : Vertex), (293 : Vertex), (297 : Vertex), (300 : Vertex), (305 : Vertex), (308 : Vertex), (312 : Vertex), (317 : Vertex), (318 : Vertex), (320 : Vertex), (323 : Vertex), (329 : Vertex), (338 : Vertex), (344 : Vertex), (353 : Vertex), (356 : Vertex), (360 : Vertex), (368 : Vertex), (377 : Vertex), (378 : Vertex), (380 : Vertex), (384 : Vertex), (390 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex), (402 : Vertex), (404 : Vertex), (407 : Vertex), (413 : Vertex), (420 : Vertex), (423 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (432 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (442 : Vertex), (455 : Vertex), (461 : Vertex), (470 : Vertex), (476 : Vertex), (485 : Vertex), (486 : Vertex), (489 : Vertex), (492 : Vertex), (498 : Vertex), (500 : Vertex), (504 : Vertex)]
def others : List Vertex := [(89 : Vertex), (93 : Vertex), (120 : Vertex), (125 : Vertex), (127 : Vertex), (257 : Vertex), (258 : Vertex), (261 : Vertex), (262 : Vertex), (263 : Vertex), (264 : Vertex), (265 : Vertex), (267 : Vertex), (268 : Vertex), (271 : Vertex), (272 : Vertex), (275 : Vertex), (276 : Vertex), (279 : Vertex), (281 : Vertex), (282 : Vertex), (285 : Vertex), (287 : Vertex), (288 : Vertex), (290 : Vertex), (293 : Vertex), (295 : Vertex), (297 : Vertex), (299 : Vertex), (300 : Vertex), (302 : Vertex), (304 : Vertex), (305 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (312 : Vertex), (314 : Vertex), (317 : Vertex), (318 : Vertex), (319 : Vertex), (320 : Vertex), (323 : Vertex), (324 : Vertex), (327 : Vertex), (329 : Vertex), (336 : Vertex), (338 : Vertex), (344 : Vertex), (345 : Vertex), (353 : Vertex), (355 : Vertex), (356 : Vertex), (358 : Vertex), (360 : Vertex), (368 : Vertex), (370 : Vertex), (376 : Vertex), (377 : Vertex), (378 : Vertex), (379 : Vertex), (380 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (388 : Vertex), (390 : Vertex), (391 : Vertex), (392 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex), (402 : Vertex), (404 : Vertex), (407 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (415 : Vertex), (416 : Vertex), (419 : Vertex), (420 : Vertex), (423 : Vertex), (425 : Vertex), (426 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (432 : Vertex), (433 : Vertex), (435 : Vertex), (436 : Vertex), (437 : Vertex), (438 : Vertex), (440 : Vertex), (442 : Vertex), (443 : Vertex), (445 : Vertex), (446 : Vertex), (448 : Vertex), (454 : Vertex), (455 : Vertex), (460 : Vertex), (461 : Vertex), (470 : Vertex), (472 : Vertex), (476 : Vertex), (481 : Vertex), (482 : Vertex), (485 : Vertex), (486 : Vertex), (488 : Vertex), (489 : Vertex), (492 : Vertex), (496 : Vertex), (498 : Vertex), (500 : Vertex), (504 : Vertex), (506 : Vertex), (508 : Vertex)]
def head : Vertex := 333
def ban : Nat := 12303636857702967606604729408227130588828397963829002976995479801303169584321288601046380665533112087214343686021814503320219200619483435486849357387399167
def reachable : Nat := 1104171072239629492969295589978715538650967856763390400728081642418594445752258375534637749536493299277775984571806733055099195083010764694383516457107456
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
theorem evenSide_length : evenSide.length = 64 := by decide

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

end Snake9.Regrowth.E112254
