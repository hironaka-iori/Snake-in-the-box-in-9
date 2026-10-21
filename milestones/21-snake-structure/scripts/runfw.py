import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)
import sys,subprocess
A=[0,1,2,5,6,13,24,26,27,28,29]; B=[3,4,7,8,9,11,12,16,20,23,31]
M=[x for x in range(32) if x not in A and x not in B]
def mk(S): return sum(1<<x for x in S)
def run(h,k,V,tmin,A,B,M,maxnodes,init,timeout=3000):
    inp=f"{h} {k} {V} {tmin} {mk(set(A)|set(M))} {mk(set(B)|set(M))} {mk(M)} {maxnodes} {init}\n"
    r=subprocess.run(['nice','-n','19',_os.path.join(_HERE, 'freewalk')],input=inp,capture_output=True,text=True,timeout=timeout)
    return r.stdout+r.stderr
if __name__=='__main__':
    h,k,V,tmin,mx,init=map(int,sys.argv[1:7])
    out=run(h,k,V,tmin,A,B,M,mx,init)
    print('\n'.join(out.strip().split('\n')[-3:]))
