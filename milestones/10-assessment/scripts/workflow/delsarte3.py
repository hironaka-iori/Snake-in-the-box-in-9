from delsarte2 import maxT
import math
for c in [8.5, 8.774, 8.906]:
    vs=[v for v in range(180,260) if maxT(v) >= c*v and 9214-35*v >= c*v]
    print('uniform T>=%.3f v : max v allowed by Delsarte+square = %d  (square alone %d)'%(c, max(vs), math.floor(9214/(35+c))))
for v in range(205,214): print(v, round(maxT(v),1), round(maxT(v)/v,3))
