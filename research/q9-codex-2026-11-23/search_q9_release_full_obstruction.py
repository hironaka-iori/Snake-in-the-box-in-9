"""Release every vertex of the matched obstruction at once, plus two path windows and the ends."""
import argparse
import json
import search_q9_anchored_sets as anchored
from search_q9_capacity_groups import GroupedSolver
from search_q9_break_matched_anchors import cases,check

class ObstructionSolver(GroupedSolver):
    def __init__(self,fixed,target,image):
        super().__init__(fixed,target)
        self.image=image
    def set_phases(self,hints):
        free={abs(lit)-1 for lit in hints}
        if self.target>=192 and self.image<=free|self.fixed:
            self.add_clause([-v-1 for v in self.image-self.fixed])
        super().set_phases(hints)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--budget",type=int,default=12000)
    parser.add_argument("--target",type=int,default=192)
    parser.add_argument("--radii",nargs="+",type=int,default=[0,2,4,6,8])
    args=parser.parse_args()
    for source,row,p,i,j,image in cases():
        a=set(image)
        for radius in args.radii:
            fixed={v for k,v in enumerate(p) if v not in a and min(abs(k-c) for c in (0,i,j,len(p)-1))>radius}
            anchored.Minicard=lambda:ObstructionSolver(fixed,args.target,a)
            st,w=anchored.search(fixed,set(p),args.target,args.budget,at_least=True)
            if w:
                check(w,args.target)
                assert fixed<=set(w)
                if len(w)>=193:assert a-set(w)
            print(json.dumps(dict(source=source,row=row,radius=radius,fixed=len(fixed),
                                  status=st,witness=w)),flush=True)
            if w and len(w)>=193:return
if __name__=="__main__":main()
