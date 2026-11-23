from inputs import D,R,norm
from collections import Counter
from check import audit
from pathlib import Path
import json,sys

def read_log(stem,wanted):
    file=D/(stem+'.log');counts=Counter();closed=set();unknown=Counter();forms=Counter();hits=[];classes=Counter()
    if not file.exists():return {}
    for line in file.open():
        s=line.split()
        if not s:continue
        if s[0]=='END':closed.add(int(s[1]))
        if s[0]=='FORM':counts[s[3]]+=1;forms[int(s[1])]+=1;unknown[int(s[1])]+=s[3]=='UNKNOWN'
        if s[0]=='PATH191':classes[norm(s[2])]+=1
        if s[0]=='FOUND':
            p,_=audit(line);hits.append(len(p)-1)
    assert not hits or max(hits)>=192
    return dict(input_rows=wanted,finished=len(closed),closed_rows=sum(unknown[i]==0 for i in closed),forms=counts,found_edges=hits,
                **(dict(real_paths=sum(classes.values()),distinct_classes=len(classes),unarchived=len(set(classes)-{norm(x) for x in (R/'q9_gap_generations/prior191.words').read_text().split()})) if classes else {}))
def main():
    datasets=[('gl_windows192',1539),('gl_windows195',479),('gl_windows196',219),('gl_prior191',131),('plus_one',131),('plus_two',1042),('add_three192',2013),('add_four195',131),('add_five196',131)]
    print(json.dumps({k:read_log(k,n) for k,n in datasets},indent=2))
if __name__=='__main__':main()
