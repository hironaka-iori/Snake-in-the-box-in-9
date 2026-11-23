import json,sys
from run import *
from retry_q9_six_cube_sites_cadical import search as cd
from search_q9_wynn_plateau import NB
def close(fixed,allowed,hint,depth=0):
    st,w=cd(fixed,hint,192,350000 if not depth else 90000,allowed)
    if st!='UNKNOWN' or depth>=4:return st,w,1
    saturated={v for v in fixed if len(set(NB[v])&fixed)==2}
    free={v for v in allowed-fixed if not saturated.intersection(NB[v]) and len(set(NB[v])&fixed)<=2}
    if not free:return st,None,1
    v=max(free,key=lambda v:(len(free.intersection(NB[v]))*(1+int(v in hint)),v));n=1;un=False
    for select in (True,False):
        t,out,attempts=close(fixed|{v} if select else fixed,allowed if select else allowed-{v},hint,depth+1);n+=attempts
        if out:return t,out,n
        un|=t=='UNKNOWN'
    return 'UNKNOWN' if un else 'UNSAT',None,n
for label,i,st,_ in map(json.loads,(D/'retry.jsonl').read_text().splitlines()):
    if st!='UNKNOWN':continue
    c=json.loads((D/f'{label}.jsonl').read_text().splitlines()[i]);fixed=unpack(int(c['fixed'],16));hint=set(bank[c['row']])|unpack(int(c['protected'],16))
    rt,w,n=close(fixed,cube,hint)
    if w:check(w);assert fixed<=set(w) and len(w)>=193
    print(json.dumps([label,i,rt,w,n]),flush=True)
