import json,random,sys
from pathlib import Path
from prepare import D,R
sys.path.insert(0,str(R))
from q9_intact_bank_search import search
cs=list(map(json.loads,(D/'cases.jsonl').read_text().splitlines()));refs=list(map(json.loads,(D/'archive_controls.jsonl').read_text().splitlines()))
mode=sys.argv[1];rng=random.Random(219581)
if mode.startswith('extra_'):
    mode=mode[6:]; refs=[]
    for ln in (D/'allmatch.paths').read_text().splitlines():
        i,n,*p=map(int,ln.split())
        if n==189:refs.append(dict(case=i,vertices=p))
for h in refs:
    p=h['vertices'];i=h['case'];c=cs[i];l=c['lo'];L=set(l+c['edge']);u,v=c['edge']
    up=[x for x in p if x>=256];hints=set(p)
    if mode=='positive':
        kept=up[3::6];perturbed=set(p)-set(up[::2]);goals=[191];configs=[(set(kept),perturbed,[x for x in up if x-256 in L],2)]
    else:
        goals=[192,191,190,189] if mode=='scores' else [192]
        configs=[]
        for y,z in ((u,v),(v,u)):
            for cross in (3,2):
                for s in ([l[0]] if cross==3 else (l[0],l[-1])):
                    ports={y+256,s+256}
                    if cross==3:ports.add(l[-1]+256)
                    shifts=ports-set(up)
                    for rad in (1,2,3,4) if mode=='search' else (2,):
                        base={x for x in up if all((x^w).bit_count()>rad for w in shifts)}
                        for opt in ([0,1,2] if mode=='search' else [0,1]):
                            k=rng.randrange(len(up)); m=rng.randrange(9,20)
                            omit=set(up[max(0,k-m):k+m]);kept=base if opt==0 else base-omit if opt==1 else {x for j,x in enumerate(up) if x in base and j%4==0}
                            configs.append((kept,hints-({x for x in up if x not in base}),list(ports),cross))
    for goal in goals:
        for j,(keep,seed,ports,cross) in enumerate(configs):
            slots={l[0]+256,l[-1]+256,u+256,v+256};ban=(set(range(256))-L)|(slots-set(ports));pins=(set(keep)-ban)|set(ports)|{u,v}
            if ban&pins:
                print(json.dumps(dict(case=i,goal=goal,cross=cross,config=j,status='conflicting_pins')),flush=True);continue
            hsafe=seed-ban
            z=search(l,goal,4500,hsafe,pins,False,forbid=ban)
            print(json.dumps(dict(case=i,goal=goal,cross=cross,config=j,pins=len(pins),branches=z),separators=(',',':')),flush=True)
            if any(b['vertices'] and len(b['vertices'])>=193 for b in z):sys.exit()
