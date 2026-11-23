"""Look for length gains from distinct motif-eligible 189-edge witnesses."""
from concurrent.futures import ThreadPoolExecutor
import json,subprocess,os
from pathlib import Path
from verify_q9_center_avoidance import verify,forms
def run(p,k):
    r=subprocess.check_output(["/tmp/q9_exchange_eligible20","9",str(k),"--fast-pairs"],input=" ".join(map(str,p))+"\n",text=True,env=dict(os.environ,Q9_AVOID_SHAPES="q9_excluded_142_lex.txt")).split()
    q=list(map(int,r[5:])) if r[1]=="FOUND" else None
    if q:verify(q);assert len(q)==len(p)+1 and len(set(p)-set(q))==k
    return [forms(p,len(p)-1)[0].hex(),k,r[1],int(r[2]),q]
if __name__=="__main__":
    seen=set();wins=[]
    with ThreadPoolExecutor(3) as pool:
        while True:
            rows=[]
            for l in Path("q9_neutral_eligible_growth.jsonl").read_text().splitlines():
                try:r=json.loads(l)
                except ValueError:continue
                if r.get("edges",0)<189:continue
                p=r["vertices"];key=forms(p,len(p)-1)[0]
                if key not in seen:seen.add(key);rows.append(p)
            if not rows:break
            for row in pool.map(lambda p:run(p,4),rows):
                print(json.dumps(row,separators=(",",":")),flush=True)
                if row[-1]:
                    wins.append(row[-1])
                    while wins:
                        p=wins.pop()
                        if len(p)>=193:raise SystemExit
                        for k in (1,2,3,4,5):
                            step=run(p,k);print(json.dumps(step,separators=(",",":")),flush=True)
                            if step[-1]:wins.append(step[-1])
