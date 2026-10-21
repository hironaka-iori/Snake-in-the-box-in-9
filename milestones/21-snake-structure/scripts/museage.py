import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)
from common import *
from bankwalk import quotient
from palette import bank_palette
from collections import Counter
b=load()
tot=Counter(); spine=Counter(); mslots=Counter(); trans=Counter(); percellM=Counter()
for idx in range(127):
    e=b[idx]; A,B,cell,hv=bank_palette(e); vs=e['vertex_sequence']
    M=set(range(32))-A-B
    ms=sum(1 for v in vs if hv(v) in M); mslots[ms]+=1
    spine[192-ms]+=1
    for c in range(16):
        percellM[sum(1 for v in vs if cell(v)==c and hv(v) in M)]+=1
    tr=sum(1 for x,y in zip(vs,vs[1:]) if cell(x)!=cell(y)); trans[tr]+=1
print('M slots used (of 160)',sorted(mslots.items()))
print('spine slots used (of 176)',sorted(spine.items()))
print('M vertices per cell',sorted(percellM.items()))
print('light transitions',sorted(trans.items()))
