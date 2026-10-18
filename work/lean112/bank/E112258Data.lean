import RegrowthParityCounts
namespace Snake9.Regrowth.E112258
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[0, 4, 36, 164, 180, 176, 48, 50, 18, 22, 150, 134, 142, 14, 10, 42, 170, 186, 190, 62, 60, 28, 24, 152, 136, 137, 9, 13, 45, 47, 175, 167, 183, 55, 53, 21, 149, 157, 189, 185, 57, 59, 27, 155, 147, 131, 3, 35, 33, 161, 225, 233, 105, 107, 75, 79, 207, 199, 215, 87, 83, 115, 243, 251, 255, 127, 125, 93, 89, 217, 209, 208, 80, 84, 116, 118, 246, 230, 238, 110, 108, 76, 204, 220, 252, 248, 120, 122, 90, 218, 202, 194, 66, 70, 326, 342, 338, 466, 467, 451, 459, 457, 461, 333, 365, 367, 495, 487, 503, 375, 373, 341]
def region : List Vertex := [(65 : Vertex), (69 : Vertex), (96 : Vertex), (101 : Vertex), (103 : Vertex), (257 : Vertex), (258 : Vertex), (261 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (268 : Vertex), (271 : Vertex), (272 : Vertex), (273 : Vertex), (275 : Vertex), (276 : Vertex), (279 : Vertex), (281 : Vertex), (282 : Vertex), (285 : Vertex), (286 : Vertex), (287 : Vertex), (288 : Vertex), (290 : Vertex), (293 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (299 : Vertex), (300 : Vertex), (302 : Vertex), (305 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (312 : Vertex), (314 : Vertex), (317 : Vertex), (319 : Vertex), (320 : Vertex), (321 : Vertex), (328 : Vertex), (330 : Vertex), (337 : Vertex), (341 : Vertex), (344 : Vertex), (347 : Vertex), (348 : Vertex), (351 : Vertex), (352 : Vertex), (353 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (360 : Vertex), (362 : Vertex), (368 : Vertex), (377 : Vertex), (379 : Vertex), (380 : Vertex), (382 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (391 : Vertex), (394 : Vertex), (396 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (404 : Vertex), (407 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (414 : Vertex), (415 : Vertex), (416 : Vertex), (418 : Vertex), (419 : Vertex), (421 : Vertex), (422 : Vertex), (424 : Vertex), (425 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (430 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (440 : Vertex), (443 : Vertex), (444 : Vertex), (447 : Vertex), (448 : Vertex), (452 : Vertex), (462 : Vertex), (468 : Vertex), (469 : Vertex), (472 : Vertex), (478 : Vertex), (479 : Vertex), (480 : Vertex), (482 : Vertex), (484 : Vertex), (488 : Vertex), (490 : Vertex), (492 : Vertex), (496 : Vertex), (497 : Vertex), (500 : Vertex), (505 : Vertex), (506 : Vertex), (509 : Vertex), (510 : Vertex)]
def oddSide : List Vertex := [(69 : Vertex), (103 : Vertex), (261 : Vertex), (268 : Vertex), (271 : Vertex), (273 : Vertex), (276 : Vertex), (279 : Vertex), (285 : Vertex), (286 : Vertex), (290 : Vertex), (295 : Vertex), (296 : Vertex), (299 : Vertex), (302 : Vertex), (307 : Vertex), (310 : Vertex), (314 : Vertex), (319 : Vertex), (321 : Vertex), (328 : Vertex), (341 : Vertex), (348 : Vertex), (351 : Vertex), (352 : Vertex), (355 : Vertex), (362 : Vertex), (379 : Vertex), (382 : Vertex), (385 : Vertex), (386 : Vertex), (388 : Vertex), (391 : Vertex), (400 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (415 : Vertex), (416 : Vertex), (419 : Vertex), (421 : Vertex), (422 : Vertex), (425 : Vertex), (428 : Vertex), (433 : Vertex), (434 : Vertex), (440 : Vertex), (443 : Vertex), (448 : Vertex), (468 : Vertex), (472 : Vertex), (478 : Vertex), (482 : Vertex), (484 : Vertex), (488 : Vertex), (496 : Vertex), (505 : Vertex), (506 : Vertex)]
def evenSide : List Vertex := [(65 : Vertex), (96 : Vertex), (101 : Vertex), (257 : Vertex), (258 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (272 : Vertex), (275 : Vertex), (281 : Vertex), (282 : Vertex), (287 : Vertex), (288 : Vertex), (293 : Vertex), (294 : Vertex), (297 : Vertex), (300 : Vertex), (305 : Vertex), (308 : Vertex), (312 : Vertex), (317 : Vertex), (320 : Vertex), (330 : Vertex), (337 : Vertex), (344 : Vertex), (347 : Vertex), (353 : Vertex), (354 : Vertex), (356 : Vertex), (360 : Vertex), (368 : Vertex), (377 : Vertex), (380 : Vertex), (384 : Vertex), (389 : Vertex), (394 : Vertex), (396 : Vertex), (399 : Vertex), (401 : Vertex), (404 : Vertex), (407 : Vertex), (414 : Vertex), (418 : Vertex), (424 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (444 : Vertex), (447 : Vertex), (452 : Vertex), (462 : Vertex), (469 : Vertex), (479 : Vertex), (480 : Vertex), (490 : Vertex), (492 : Vertex), (497 : Vertex), (500 : Vertex), (509 : Vertex), (510 : Vertex)]
def others : List Vertex := [(65 : Vertex), (69 : Vertex), (96 : Vertex), (101 : Vertex), (103 : Vertex), (257 : Vertex), (258 : Vertex), (261 : Vertex), (263 : Vertex), (264 : Vertex), (267 : Vertex), (268 : Vertex), (271 : Vertex), (272 : Vertex), (273 : Vertex), (275 : Vertex), (276 : Vertex), (279 : Vertex), (281 : Vertex), (282 : Vertex), (285 : Vertex), (286 : Vertex), (287 : Vertex), (288 : Vertex), (290 : Vertex), (293 : Vertex), (294 : Vertex), (295 : Vertex), (296 : Vertex), (297 : Vertex), (299 : Vertex), (300 : Vertex), (302 : Vertex), (305 : Vertex), (307 : Vertex), (308 : Vertex), (310 : Vertex), (312 : Vertex), (314 : Vertex), (317 : Vertex), (319 : Vertex), (320 : Vertex), (321 : Vertex), (328 : Vertex), (330 : Vertex), (337 : Vertex), (344 : Vertex), (347 : Vertex), (348 : Vertex), (351 : Vertex), (352 : Vertex), (353 : Vertex), (354 : Vertex), (355 : Vertex), (356 : Vertex), (360 : Vertex), (362 : Vertex), (368 : Vertex), (377 : Vertex), (379 : Vertex), (380 : Vertex), (382 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (388 : Vertex), (389 : Vertex), (391 : Vertex), (394 : Vertex), (396 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (404 : Vertex), (407 : Vertex), (409 : Vertex), (410 : Vertex), (412 : Vertex), (414 : Vertex), (415 : Vertex), (416 : Vertex), (418 : Vertex), (419 : Vertex), (421 : Vertex), (422 : Vertex), (424 : Vertex), (425 : Vertex), (427 : Vertex), (428 : Vertex), (429 : Vertex), (430 : Vertex), (433 : Vertex), (434 : Vertex), (435 : Vertex), (437 : Vertex), (438 : Vertex), (440 : Vertex), (443 : Vertex), (444 : Vertex), (447 : Vertex), (448 : Vertex), (452 : Vertex), (462 : Vertex), (468 : Vertex), (469 : Vertex), (472 : Vertex), (478 : Vertex), (479 : Vertex), (480 : Vertex), (482 : Vertex), (484 : Vertex), (488 : Vertex), (490 : Vertex), (492 : Vertex), (496 : Vertex), (497 : Vertex), (500 : Vertex), (505 : Vertex), (506 : Vertex), (509 : Vertex), (510 : Vertex)]
def head : Vertex := 341
def ban : Nat := 8061730456076486742576076794131503540159867514299157821751797607574105401963855829597972046769544608429892130719936490265607815914100046593542446244691967
def reachable : Nat := 5346077473866110356997948204074342587319498306293235555971763836147658628109691090664796178489060272594619703693157054108661366878039863461492761397559296
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

end Snake9.Regrowth.E112258
