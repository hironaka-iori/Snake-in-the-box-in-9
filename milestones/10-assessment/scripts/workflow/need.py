import json, math
from delsarte2 import maxT
rows = json.load(open('census.json'))
bank_k = 18428/192 - 70
twoT = [2*r['T']/r['v'] for r in rows]; Ev = [r['E']/r['v'] for r in rows]
print('bank: (2T+E)/v = %.4f exactly; 2T/v in [%.3f, %.3f] mean %.3f; E/v in [%.3f, %.3f] mean %.3f' % (bank_k, min(twoT), max(twoT), sum(twoT)/len(twoT), min(Ev), max(Ev), sum(Ev)/len(Ev)))
print('  L   v*=L+2  need (2T+E)/v >  %bank   need T/v (E>=0 dropped) >   need T/v with Delsarte >  min E/v needed if 2T/v=17.0 (bank min)')
for L in (191, 192, 196, 200, 205, 210, 220, 230, 240, 245):
    v = L + 2
    k = 18428/v - 70
    tD = maxT(v)
    print('%4d  %4d    %7.3f         %5.1f%%    %7.3f                     %7.3f                 %7.3f' % (L, v, k, 100*k/bank_k, k/2, min(tD, 9214-35*v)/v, max(0, k-17.0)))
