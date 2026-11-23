"""Independently reconstruct the two eight-dimensional arms of the 191-edge join."""
import json
from itertools import combinations
from pathlib import Path
def verify(p,dim):
    assert all(type(v)==int and 0<=v<1<<dim for v in p) and len(set(p))==len(p)
    for (i,x),(j,y) in combinations(enumerate(p),2):
        assert ((x^y).bit_count()==1)==(j-i==1)
def main():
    flag,*v=Path("q9_transverse_q8_control.log").read_text().split()
    p=list(map(int,v));assert flag=="FOUND" and len(p)==192;verify(p,9)
    crossings=[j for j in range(191) if p[j]^p[j+1]==256]
    assert len(crossings)==1 and p[0]<256
    cut=crossings[0];a=p[:cut+1];b=[x^256 for x in p[cut+1:]]
    verify(a,8);verify(b,8)
    assert set(a)&set(b)=={a[-1]} and a[-1]==b[0]
    assert (len(a)-1,len(b)-1)==(96,94)
    def word(q):return "".join(str((v^w).bit_length()-1) for v,w in zip(q,q[1:]))
    return {"dimension":9,"edges":len(p)-1,"vertices":p,"coordinate_labels":"0-based","left_8_cube_vertices":a,"right_8_cube_vertices":b,"left_transitions":word(a),"right_transitions":word(b),"crossing_coordinate":8,"shared_projection":a[-1],"checked_pairs":len(p)*(len(p)-1)//2}
if __name__=="__main__":print(json.dumps(main(),indent=2))
