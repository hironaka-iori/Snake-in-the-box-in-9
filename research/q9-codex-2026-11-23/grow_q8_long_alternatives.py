"""Search for alternative 97-98 edge shapes through deeper Q8 vertex exchanges."""
import json,subprocess
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from verify_q9_center_avoidance import forms,verify
def word(p):return forms(p,len(p)-1)[0]
def work(job):
    p,k,g=job
    lines=subprocess.check_output(["/tmp/q8_all_fast_exchange20","8",str(k),f"--all-fast={g}"],input=" ".join(map(str,p))+"\n",text=True).splitlines()
    out={}
    for l in lines[:-1]:
        marker,*v=l.split();assert marker=="PATH";q=list(map(int,v));verify(q);assert len(q)==len(p)+g and len(set(p)-set(q))==k
        out.setdefault(word(q),q)
    assert lines[-1].split()[1]=="NO"
    return word(p),k,g,out
if __name__=="__main__":
    old={}
    for name in ("q8_joint_even_arms.txt","q8_exchange_new_rooted_arms.txt","q8_exchange_second_rooted_arms.txt"):
        for w in Path(name).read_text().split():
            if len(w)<96:continue
            p=[0]
            for x in w:p.append(p[-1]^(1<<int(x)))
            old.setdefault(word(p),p)
    todo=[(p,k,g) for p in old.values() if len(p)==97 for k,g in [(4,1),(5,1)]]+[(p,6,g) for p in old.values() if len(p)>=98 for g in (0,1) if len(p)+g<=99]
    seen=set(old)
    with ThreadPoolExecutor(2) as pool:
        for key,k,g,found in pool.map(work,todo):
            for s,w in found.items():
                if s not in seen:
                    seen.add(s);print(json.dumps({"source":key.hex(),"k":k,"gain":g,"edges":len(w)-1,"vertices":w},separators=(",",":")),flush=True)
            print(json.dumps({"done":key.hex(),"k":k,"gain":g,"hits":len(found)}),flush=True)
