import ReferencePicks

namespace Snake9.Reference85
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def picks21 : List Pick := [
(false,1215),
(false,1216),
(false,1217),
(false,1218),
(false,1219),
(false,1220),
(false,1221),
(false,1222),
(false,1223),
(false,1224),
(false,1225),
(false,1226),
(false,1227),
(true,724),
(true,725),
(false,1228),
(false,1229),
(false,1230),
(false,1231),
(false,1232),
(false,1233),
(false,1234),
(false,1235),
(false,1236),
(false,1237),
(false,1238),
(false,1239),
(true,730),
(false,1240),
(false,1241),
(false,1242),
(true,731),
(false,1243),
(false,1244)
]

def keys21 : List Key := [
([0,1,2,3,4,5],[3,5,3,6,3]),
([0,1,2,3,4,5],[3,5,4,3,4]),
([0,1,2,3,4,5],[3,5,4,3,5]),
([0,1,2,3,4,5],[3,5,4,4,4]),
([0,1,2,3,4,5],[3,5,5,2,4]),
([0,1,2,3,4,5],[3,5,5,2,5]),
([0,1,2,3,4,5],[3,6,2,3,4]),
([0,1,2,3,4,5],[3,6,2,3,5]),
([0,1,2,3,4,5],[3,6,2,4,4]),
([0,1,2,3,4,5],[3,6,2,5,4]),
([0,1,2,3,4,5],[3,6,2,6,3]),
([0,1,2,3,4,5],[3,6,2,6,4]),
([0,1,2,3,4,5],[3,6,3,2,4]),
([0,1,2,3,4,5],[3,6,3,2,5]),
([0,1,2,3,4,5],[3,6,3,3,4]),
([0,1,2,3,4,5],[3,6,3,4,4]),
([0,1,2,3,4,5],[3,6,4,3,4]),
([0,1,2,3,4,5],[3,6,5,1,5]),
([0,1,2,3,4,5],[3,6,5,1,6]),
([0,1,2,3,4,5],[4,2,3,6,4]),
([0,1,2,3,4,5],[4,2,3,6,5]),
([0,1,2,3,4,5],[4,2,6,2,4]),
([0,1,2,3,4,5],[4,3,2,6,4]),
([0,1,2,3,4,5],[4,3,2,6,5]),
([0,1,2,3,4,5],[4,3,4,4,4]),
([0,1,2,3,4,5],[4,4,2,6,4]),
([0,1,2,3,4,5],[4,4,2,6,5]),
([0,1,2,3,4,5],[4,4,3,4,4]),
([0,1,2,3,4,5],[4,5,2,4,5]),
([0,1,2,3,4,5],[4,5,2,6,4]),
([0,1,2,3,4,5],[4,6,2,3,5]),
([0,1,2,3,4,5],[4,6,3,2,5]),
([0,1,2,3,4,5],[4,6,5,1,6]),
([0,1,2,3,4,5],[5,6,2,2,6])
]

theorem picks21_valid : picks21.all pickValid = true := by decide +kernel
theorem keys21_exact : keys21 = picks21.map pickKey := by decide +kernel
theorem keys21_valid : keys21.all keyValid = true := by decide +kernel
theorem keys21_covered : keys21.all keyCovered = true := by
  rw [keys21_exact]
  exact picks_covered picks21 picks21_valid

#print axioms picks21_valid
#print axioms keys21_exact
#print axioms keys21_valid
#print axioms keys21_covered
end Snake9.Reference85
