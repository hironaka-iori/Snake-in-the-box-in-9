import FinitePotential
namespace Snake9.CriticalFamily61.Split62Potential9
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def edges : List (Nat × Nat × Nat) := [(0, 28, 720), (1, 27, 240), (0, 32, 720), (1, 30, 240), (2, 20, 720), (2, 19, 720), (2, 22, 720), (3, 24, 730), (3, 26, 734), (4, 41, 366), (5, 35, 720), (5, 34, 720), (5, 37, 720), (6, 38, 720), (6, 40, 720), (7, 46, 720), (7, 44, 720), (7, 45, 720), (7, 48, 720), (8, 10, 490), (9, 11, 125), (10, 31, 727), (11, 42, 604), (12, 0, 120), (13, 1, 240), (14, 2, 120), (15, 3, 248), (17, 4, 486), (16, 5, 120), (16, 6, 120), (16, 7, 120), (18, 30, 240), (19, 36, 720), (20, 39, 720), (21, 43, 240), (22, 47, 720), (23, 8, 368), (24, 9, 725), (26, 9, 725), (25, 8, 371), (26, 9, 725), (28, 13, 720), (29, 12, 600), (27, 17, 720), (29, 16, 600), (30, 17, 720), (33, 16, 600), (32, 13, 720), (33, 12, 600), (33, 14, 600), (31, 15, 248), (30, 17, 720), (33, 16, 600), (34, 36, 720), (35, 39, 720), (36, 43, 240), (37, 47, 720), (38, 21, 720), (39, 18, 240), (40, 21, 720), (41, 25, 726), (41, 23, 726), (41, 25, 726), (42, 33, 720), (43, 30, 240), (42, 29, 720), (43, 27, 240), (42, 33, 720), (43, 30, 240), (44, 47, 720), (45, 36, 720), (46, 39, 720), (47, 43, 240), (48, 47, 720)]
def potential : List Nat := [3019, 6850, 3019, 0, 6001, 3019, 3019, 3019, 5432, 9254, 5309, 1831, 10542, 11973, 10542, 4963, 10542, 6204, 6850, 7496, 7496, 11973, 7496, 7995, 4677, 7995, 4757, 1727, 7496, 8465, 1727, 9926, 7496, 8465, 7496, 7496, 11973, 7496, 7496, 11973, 7496, 3398, 3988, 6850, 7496, 7496, 7496, 11973, 7496]
def cycle : List (Nat × Nat × Nat) := [(17, 4, 486), (4, 41, 366), (41, 23, 726), (23, 8, 368), (8, 10, 490), (10, 31, 727), (31, 15, 248), (15, 3, 248), (3, 24, 730), (24, 9, 725), (9, 11, 125), (11, 42, 604), (42, 33, 720), (33, 16, 600), (16, 5, 120), (5, 35, 720), (35, 39, 720), (39, 18, 240), (18, 30, 240), (30, 17, 720)]
theorem checked : checkEdges 9923 20 potential edges=true := by decide +kernel
theorem every_closed_walk (n : Nat) (f w : Nat → Nat)
    (h : ∀ i<n, (f i,f (i+1),w i)∈edges) (hc : f n=f 0) :
    n*9923 ≤ 20*(∑ i ∈ Finset.range n, w i) := by
  apply closed_bound 9923 20 n (fun x => potential.getD x 0) f w ?_ hc
  intro i hi
  exact edge_of_check checked (h i hi)
theorem attaining_cycle : (List.range cycle.length).all (fun i =>
    edges.contains (cycle.getD i (0,0,0)) &&
    decide ((cycle.getD i (0,0,0)).2.1=(cycle.getD ((i+1)%cycle.length) (0,0,0)).1))=true := by decide +kernel
theorem attainment : 20*(cycle.map (fun e => e.2.2)).sum=9923*cycle.length := by decide +kernel
#print axioms checked
#print axioms every_closed_walk
#print axioms attaining_cycle
#print axioms attainment
end Snake9.CriticalFamily61.Split62Potential9
