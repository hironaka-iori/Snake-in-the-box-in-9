"""Use the independent SAT completion to retry bounded four-state DFS cases."""
import json,sys
from search_q9_checkerboard_walk import half_completion
from verify_q9_center_avoidance import verify
def main():
    records={}
    for line in open('q9_projected_checkerboard_sets.txt'):
        i,c,*A=map(int,line.split());records[i]=set(A)
    prior=set()
    for f in sys.argv[2:]:
        for i,v,st,_ in map(json.loads,open(f)):
            if st!='UNKNOWN':prior.add((i,v))
    for line in open('q9_checkerboard_all_toggles.log'):
        fields=line.split()
        if fields[0]!='UNKNOWN':continue
        i,v=map(int,fields[1:])
        if (i,v) in prior:continue
        A=records[i]^{v}
        st,w=half_completion(A,192,int(sys.argv[1]),A)
        print(json.dumps([i,v,st,w],separators=(',',':')),flush=True)
        if w:verify(w);return
if __name__=='__main__':main()
