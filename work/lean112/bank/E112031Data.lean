import RegrowthParityCounts
namespace Snake9.Regrowth.E112031
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def pre : Array Nat := #[376, 377, 379, 383, 375, 373, 357, 356, 364, 366, 362, 354, 355, 99, 227, 226, 234, 238, 236, 228, 244, 245, 247, 255, 251, 249, 248, 184, 188, 190, 182, 178, 179, 177, 161, 165, 173, 175, 171, 427, 443, 447, 439, 437, 436, 420, 422, 486, 487, 495, 493, 509, 508, 510, 506, 498, 499, 497, 481, 480, 488, 424, 296, 288, 289, 305, 307, 306, 310, 318, 316, 317, 301, 303, 295, 39, 55, 53, 52, 36, 44, 46, 42, 58, 59, 57, 41, 105, 109, 125, 124, 126, 118, 114, 112, 80, 84, 85, 87, 95, 91, 75, 11, 15, 13, 29, 28, 24, 280, 281, 283, 287]
def region : List Vertex := [(0 : Vertex), (1 : Vertex), (2 : Vertex), (6 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (65 : Vertex), (66 : Vertex), (70 : Vertex), (72 : Vertex), (76 : Vertex), (78 : Vertex), (128 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (197 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (266 : Vertex), (268 : Vertex), (270 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (287 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (391 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex)]
def oddSide : List Vertex := [(1 : Vertex), (2 : Vertex), (19 : Vertex), (22 : Vertex), (70 : Vertex), (76 : Vertex), (128 : Vertex), (131 : Vertex), (134 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (148 : Vertex), (151 : Vertex), (155 : Vertex), (193 : Vertex), (199 : Vertex), (200 : Vertex), (205 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (259 : Vertex), (261 : Vertex), (262 : Vertex), (266 : Vertex), (268 : Vertex), (276 : Vertex), (279 : Vertex), (321 : Vertex), (327 : Vertex), (328 : Vertex), (333 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (385 : Vertex), (386 : Vertex), (391 : Vertex), (397 : Vertex), (398 : Vertex), (400 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (460 : Vertex), (468 : Vertex), (471 : Vertex), (472 : Vertex), (475 : Vertex)]
def evenSide : List Vertex := [(0 : Vertex), (6 : Vertex), (17 : Vertex), (18 : Vertex), (65 : Vertex), (66 : Vertex), (72 : Vertex), (78 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (136 : Vertex), (142 : Vertex), (144 : Vertex), (149 : Vertex), (153 : Vertex), (154 : Vertex), (159 : Vertex), (192 : Vertex), (197 : Vertex), (198 : Vertex), (201 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (260 : Vertex), (270 : Vertex), (277 : Vertex), (287 : Vertex), (320 : Vertex), (326 : Vertex), (329 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (387 : Vertex), (389 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (399 : Vertex), (401 : Vertex), (402 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (452 : Vertex), (459 : Vertex), (462 : Vertex), (464 : Vertex), (469 : Vertex), (470 : Vertex), (473 : Vertex), (479 : Vertex)]
def others : List Vertex := [(0 : Vertex), (1 : Vertex), (2 : Vertex), (6 : Vertex), (17 : Vertex), (18 : Vertex), (19 : Vertex), (22 : Vertex), (65 : Vertex), (66 : Vertex), (70 : Vertex), (72 : Vertex), (76 : Vertex), (78 : Vertex), (128 : Vertex), (130 : Vertex), (131 : Vertex), (132 : Vertex), (134 : Vertex), (135 : Vertex), (136 : Vertex), (137 : Vertex), (138 : Vertex), (140 : Vertex), (142 : Vertex), (144 : Vertex), (148 : Vertex), (149 : Vertex), (151 : Vertex), (153 : Vertex), (154 : Vertex), (155 : Vertex), (159 : Vertex), (192 : Vertex), (193 : Vertex), (197 : Vertex), (198 : Vertex), (199 : Vertex), (200 : Vertex), (201 : Vertex), (205 : Vertex), (207 : Vertex), (209 : Vertex), (210 : Vertex), (211 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (221 : Vertex), (222 : Vertex), (258 : Vertex), (259 : Vertex), (260 : Vertex), (261 : Vertex), (262 : Vertex), (266 : Vertex), (268 : Vertex), (270 : Vertex), (276 : Vertex), (277 : Vertex), (279 : Vertex), (320 : Vertex), (321 : Vertex), (326 : Vertex), (327 : Vertex), (328 : Vertex), (329 : Vertex), (333 : Vertex), (335 : Vertex), (337 : Vertex), (338 : Vertex), (339 : Vertex), (342 : Vertex), (346 : Vertex), (348 : Vertex), (349 : Vertex), (350 : Vertex), (384 : Vertex), (385 : Vertex), (386 : Vertex), (387 : Vertex), (389 : Vertex), (391 : Vertex), (393 : Vertex), (394 : Vertex), (396 : Vertex), (397 : Vertex), (398 : Vertex), (399 : Vertex), (400 : Vertex), (401 : Vertex), (402 : Vertex), (403 : Vertex), (406 : Vertex), (410 : Vertex), (412 : Vertex), (413 : Vertex), (414 : Vertex), (450 : Vertex), (451 : Vertex), (452 : Vertex), (453 : Vertex), (457 : Vertex), (458 : Vertex), (459 : Vertex), (460 : Vertex), (462 : Vertex), (464 : Vertex), (468 : Vertex), (469 : Vertex), (470 : Vertex), (471 : Vertex), (472 : Vertex), (473 : Vertex), (475 : Vertex), (479 : Vertex)]
def head : Vertex := 287
def ban : Nat := 13407807928236087838402113392769204159428661719123263322288544514830597255922592007074854013921550083073958621366521313317617049019207944751893562547896248
def reachable : Nat := 1706509261171911605436641968050704101469130055435016928891166774150954969727020284245353344616073236819964737536136833792738625194540086458187847
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
theorem oddSide_length : oddSide.length = 57 := by decide
theorem evenSide_length : evenSide.length = 60 := by decide

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

end Snake9.Regrowth.E112031
