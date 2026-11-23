"""Equal-size exchanges on 189-edge seeds and on their two 188-edge trims."""
from pathlib import Path
from collections import deque
from concurrent.futures import ThreadPoolExecutor
import json,subprocess,os
from verify_q9_center_avoidance import verify,forms
blocked={bytes(map(int,s)) for s in Path("q9_excluded_142_lex.txt").read_text().split()}
def moves(p,k,g):
    cmd=["/tmp/q9_exchange_eligible20","9",str(k),"--fast-pairs" if g else "0"]
    raw=subprocess.check_output(cmd,input=" ".join(map(str,p))+"\n",text=True,env=dict(os.environ,Q9_AVOID_SHAPES="q9_excluded_142_lex.txt"))
    out={}
    for line in raw.splitlines():
        s=line.split()
        if s[0]=="PATH":v=list(map(int,s[1:]))
        elif s[1]=="FOUND":v=list(map(int,s[5:]))
        else:continue
        verify(v);assert len(v)==len(p)+g and len(set(p)-set(v))==k and blocked.isdisjoint(forms(v,142))
        out.setdefault(forms(v,len(v)-1)[0],v)
    return list(out.items())
if __name__=="__main__":
    seeds=[r["vertices"] for r in json.load(open("q9_center_avoidance_verified.json"))["new_witnesses"]]
    known=set();q=deque()
    def insert(p,h=False):
        key=forms(p,len(p)-1)[0]
        if key in known:return False
        known.add(key);(q.appendleft if h else q.append)(p);return True
    for p in seeds:insert(p)
    for p in seeds:
        for trimmed in (p[1:],p[:-1]):insert(trimmed)
    with ThreadPoolExecutor(3) as pool:
        for i in range(900):
            if not q:break
            p=q.popleft();tasks=[(k,g) for k in (1,2,3) for g in (0,1)]
            if len(p)>=191:tasks.extend([(4,1),(5,1)])
            for (k,g),outs in zip(tasks,pool.map(lambda a:moves(p,*a),tasks)):
                for key,v in outs:
                    if insert(v,g>0):
                        print(json.dumps({"edges":len(v)-1,"deletions":k,"gain":g,"vertices":v},separators=(",",":")),flush=True)
                        if len(v)>=193:raise SystemExit
            if i%5==0:print(json.dumps({"searched":i+1,"frontier":len(q),"known":len(known)}),flush=True)
