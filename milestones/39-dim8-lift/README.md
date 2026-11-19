# Milestone 39: lifting dimension-8 facts to a(9) (work in progress)

Interim notes; the full findings will replace this file. **No bound is claimed.**

- Layering (milestone 29) reduces everything to one number: g8(13), the largest induced linear forest
  of Q8 with at most 13 paths. With the Lean cap a(9) <= 231: a(9) <= 229 / 227 / 225 / 223 follows
  from g8(13) <= 115 / 114 / 113 / 112. Proved so far: g8(13) <= 121; lower bound 112.
- SDP (any moment relaxation whose constraints involve fewer than d vertices): explicit feasible 0/1
  points give value >= 254 edges for d < 8, >= 222 for d < 14, >= 206 for d < 26
  (`scripts/sdp_ceiling.py`, `data/sdp_ceiling.json`).
- Exhaustive search in Q9: Knuth estimate ~6e40 nodes at target 222 vertices with the free-vertex
  prune (2e22 for Q8 at 100) (`scripts/knuth.c`, `data/knuth_raw.txt`).
- Orbit enumeration: Q5 forests with >= 15 vertices: 35 orbits under B5; Q6 with >= 30: 222 orbits
  (`scripts/enumk.c`, `scripts/enum6.c`); basis of a largest-subcube cube-and-conquer (`scripts/cubes.py`).
