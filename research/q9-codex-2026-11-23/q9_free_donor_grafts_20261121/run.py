import json,sys
from collections import Counter
from pathlib import Path
from prepare import D,R,bank,unpack,check
sys.path.insert(0,str(R))
from retry_q9_six_cube_sites_cadical import search as cad
from search_q9_anchored_sets import search as mini
cube=set(range(512))
def solve(fixed,hint,goal,budget,backend):
    return cad(fixed,hint,goal,budget,cube) if backend=='cadical' else mini(fixed,hint,goal,budget,allowed=cube,at_least=True)
def run():
    label,method,budget,goal,start,stop=sys.argv[1:];budget,goal,start,stop=map(int,(budget,goal,start,stop));src=(D/f'{label}.jsonl').read_text().splitlines()
    for i,line in enumerate(src):
        if not start<=i<stop:continue
        c=json.loads(line);fix=unpack(int(c['fixed'],16));don=unpack(int(c['protected'],16));hint=set(bank[c['row']])|don
        st,w=solve(fix,hint,goal,budget,method)
        if w:check(w);assert len(w)>=goal+1 and fix<=set(w)
        print(json.dumps([i,len(fix),st,w],separators=(',',':')),flush=True)
        if w and goal>=192:return
if __name__=='__main__':run()
