from collections import Counter
import json
from prepare import D,CUBE,unhex,paircheck
from run import solve
sample=[(i,c) for i,l in enumerate((D/'cases.jsonl').open()) if (c:=json.loads(l))['anchors']==145]
sample.sort(key=lambda x:(x[1]['overlap'],x[1]['line']))
for goal in (191,190,189,188,187,186):
    counts=Counter()
    for i,c in sample[:280]:
        fixed,host=map(unhex,[c['fixed'],c['host']])
        st,w=solve('minicard',fixed,host,goal,12000);counts[st]+=1
        if w and set(w)-host:
            paircheck(w);assert len(w)>=goal+1 and fixed<=set(w)
            print(json.dumps(dict(goal=goal,actual=len(w)-1,row=i,line=c['line'],counts=counts,outside_host=sorted(set(w)-host),witness=w)),flush=True)
            quit()
    print(json.dumps(dict(goal=goal,counts=counts)),flush=True)
