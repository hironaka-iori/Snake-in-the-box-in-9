from collections import Counter,defaultdict
from pathlib import Path
import json
from prepare import D,R,bank,paircheck
def norm(w):
    m={};return tuple(m.setdefault(c,len(m)) for c in w)
def canonical(p):
    w=[(v^u).bit_length()-1 for v,u in zip(p,p[1:])]
    return ''.join(map(str,min(norm(w),norm(w[::-1]))))
def clear(p):
    ids={v:i for i,v in enumerate(p)}
    assert len(ids)==len(p) and all(0<=v<512 for v in p)
    assert all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
    assert sum((v^1<<j) in ids for v in p for j in range(9))==2*(len(p)-1)
def roots(name):return [list(map(int,l.split())) for l in (D/(name+'.dat')).open()]
records={i:l.split() for i,l in enumerate((R/'q8_near_host_placements.log').open(),1) if l.startswith('HOST ')}
hosts={};reports={};resolved={};recovered=defaultdict(set);geometry=Counter()
for field,inname in [('control','controls'),('known','knownroots'),('borrowed','borrowed'),('grafted','grafted'),('retry','retry'),('deep','deep')]:
    data=roots(inname);rows={};nodes=0;cut=0;mx=0;outs=Counter();spent=Counter();ranges=[];cntrl=[]
    for l in (D/(field+'.log')).open():
        t=l.split();i=int(t[1])
        if t[0]=='ROW':
            idx,ln,e,nroot,visit,stop,best,ext,win=map(int,t[1:]);assert idx==i
            job=data[i];orig,e0,cap,tag,nh=job[:5];h=frozenset(job[5:5+nh]);p=tuple(job[6+nh:]);assert orig==ln and e0==e and len(p)==nroot==job[5+nh]
            if ln not in hosts:
                _,a,b,trans,k,pm=records[ln];reverse=[pm.index(str(j)) for j in range(8)]
                bset={256+(int(trans)^sum(((x>>j)&1)<<i for i,j in enumerate(reverse))) for x in bank[int(b)]}
                hosts[ln]=frozenset(bank[int(a)])|bset;assert len(set(bank[int(a)])&{v-256 for v in bset})==int(k)
            assert hosts[ln]==h;clear(p);initial=len(set(p)-h);assert initial<=e
            rows[i]=(p,h,e,best,ext,win);nodes+=visit;cut+=stop;mx=max(mx,best-1);spent[ext]+=int(best==192);ranges.append(nroot-1)
            if field!='control':
                k=(ln,e,min(p,p[::-1]));resolved[k]=resolved.get(k,True) and bool(stop)
                geometry[initial]+=1
            else: assert win==1;cntrl.append(ext)
        elif t[0]=='PATH':
            ext=int(t[2]);q=list(map(int,t[3:]));p,h,e,best,observed,win=rows[i]
            assert len(q)==best and len(set(q)-h)==observed==ext<=e;paircheck(q)
            offset=q.index(p[0]);assert q[offset:offset+len(p)]==list(p)
            if field!='control':recovered[len(q)-1].add(canonical(q))
    assert len(rows)==len(data)
    reports[field]=dict(cases=len(rows),tree_nodes=nodes,cutoffs=cut,max_edges=mx,root_edge_range=[min(ranges),max(ranges)],outside_on_returned191=dict(spent))
    if field=='control':reports[field]['control_outside_counts']=cntrl
summary={}
for n,ws in recovered.items():
    ref=R/'q9_gap_generations'/f'prior{n}.words'
    if ref.exists():
        known=set(ref.read_text().split());new=ws-known
        (D/f'new{n}.words').write_text(''.join(w+'\n' for w in sorted(new)))
        summary[n]=dict(count=len(ws),outside_comparison=len(new),reference=len(known))
    else:summary[n]=dict(count=len(ws))
print(json.dumps(dict(host_rows=len(hosts),distinct_target_specs=len(resolved),target_nodes=sum(x['tree_nodes'] for f,x in reports.items() if f!='control'),target_cutoff_after_retries=sum(resolved.values()),exhausted_target_specs=len(resolved)-sum(resolved.values()),reports=reports,returned_classes=summary,small_controls=json.load(open(D/'smallcheck.json'))),indent=2))
