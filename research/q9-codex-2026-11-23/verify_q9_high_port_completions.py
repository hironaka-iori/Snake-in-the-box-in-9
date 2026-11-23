"""Summarize fixed-face 192 searches; reconstruct endpoint choices independently."""
import argparse
from collections import Counter,defaultdict
from itertools import combinations
from pathlib import Path
import gzip,hashlib,json,random
from verify_q9_intact98_all_crossings import integer_bound,check
from search_q9_high_port_dual_completion import verify

def allowed(low):
    leaves=[];forced=set();ends=[]
    for v in low:
        degree=sum(v^(1<<d) in low for d in range(8))
        if degree==0:forced.add(v)
        elif degree==1:leaves.append(v)
        else:check(degree==2,'nonlinear lower facet')
    remaining=set(low);components=[]
    while remaining:
        q=[remaining.pop()]
        for x in q:
            neighbors=remaining&{x^(1<<d) for d in range(8)}
            remaining-=neighbors;q.extend(neighbors)
        check(any(x in forced or x in leaves for x in q),'cycle in lower facet')
        components.append(set(q))
    for h in (0,1):
        for n in range(3-len(forced)):
            for omit in combinations([v for v in leaves if v.bit_count()%2==h],n):
                if any(v.bit_count()%2!=h for v in forced):continue
                ports=forced|(set(leaves)-set(omit))
                if not all(c&ports for c in components):continue
                full=(2,0) if h==0 else (0,2)
                yield tuple(sorted(ports)),full

def main():
    p=argparse.ArgumentParser();p.add_argument('--bank',type=Path,default=Path('/private/tmp/q9_high_port_forests20.txt'))
    p.add_argument('--keep-donors',type=Path);p.add_argument('--replay',action='store_true')
    p.add_argument('pairs',nargs='+',help='alternating trials JSONL and certificate gzip files')
    a=p.parse_args();check(len(a.pairs)%2==0,'need file pairs')
    logs=[[json.loads(l) for l in open(f)] for f in ('q9_port_highdim_free_face.jsonl','q9_port_highdim_exact192.jsonl')]
    exact={r[0]:r[-2] for r in logs[1][1:]}
    if a.bank.suffix=='.gz':
        bank={i:s for i,s in map(json.loads,gzip.open(a.bank,'rt'))}
    else:
        raw=a.bank.read_text().splitlines()
        bank={r[0]:list(map(int,raw[r[0]].split()[1:])) for r in logs[0][1:] if r[-2]=='UNKNOWN' and exact[r[0]]=='UNKNOWN'}
    for i,n,hashval,st,w in logs[0][1:]:
        if i in bank:check(len(set(bank[i]))==n and hashlib.sha256(bytes(bank[i])).hexdigest()==hashval and st==exact[i]=='UNKNOWN','donor hash/status mismatch')
    check(len(bank)==290,'wrong donor count')
    if a.keep_donors:
        with gzip.open(a.keep_donors,'wt') as f:
            for i,s in sorted(bank.items()):f.write(json.dumps([i,s],separators=(',',':'))+'\n')
    expected={i:set(allowed(set(v))) for i,v in bank.items()}
    totals=Counter();processed=defaultdict(dict);replayed=0;positive=[];control=[]
    for f,g in zip(a.pairs[::2],a.pairs[1::2]):
        certs={}
        for r in map(json.loads,gzip.open(g,'rt')):
            i=r['index'];k=(tuple(r['ports']),tuple(r['full']))
            check((i,k) not in certs,'repeated certificate');certs[i,k]=r
        for r in map(json.loads,open(f)):
            i=r['index'];k=(tuple(r['ports']),tuple(r['full']));totals[r['status']]+=1
            if i=='control':low={v for v in logs[0][0][-1] if v<256}
            else:
                low=set(bank[i]);check(k in expected[i] and len(expected[i])==r['branch_count'],'bad branch')
            low_tips={v for v in low if sum(v^(1<<d) in low for d in range(8))+int(v in k[0])==1}
            counts=tuple(k[1][h]-sum(v.bit_count()%2==h for v in low_tips) for h in (0,1))
            balance=sum((-1)**v.bit_count() for v in low)-(k[1][0]-k[1][1])//2
            check(counts==tuple(r["ends"]) and balance==r["delta"],"wrong upper endpoint/colour conditions")
            if r['status']=='EMPTY':
                axes=list(combinations(range(8),3));random.Random(403215).shuffle(axes)
                zero=dict(axes=axes[:6],scale=1,end_weights=[0,0],balance_weight=0,weights=[])
                try:integer_bound(zero,low,set(k[0]),tuple(r['ends']),r['delta'])
                except ValueError as e:check(str(e) in ('no possible state for required upper vertex','infeasible affine face'),'unexpected empty')
                else:raise ValueError('nonempty model recorded empty')
            else:
                c=certs.pop((i,k));check(c['low']==sorted(low) and c['numerator']==r['numerator'] and c['upper']==r['upper'],'certificate does not match')
                if a.replay:
                    v=integer_bound(c['cert'],low,set(k[0]),tuple(r['ends']),r['delta'])
                    check(v==c['numerator'],'integer replay mismatch');replayed+=1
                num=c['numerator'];scale=c['cert']['scale'];bound=len(low)-1+num//scale
                bound-=int((bound-r['goal'])%2!=0)
                check(bound==r['upper'],'bad integer edge bound')
                if r['status']=='DUAL':check(bound<r['goal'],'false dual')
                else:check(bound>=r['goal'] and r['status'] in ('FOUND','EXHAUSTED','UNKNOWN'),'invalid search status')
            if r['status']=='FOUND':
                verify(r['witness'],low,k[0],k[1],r['goal'])
                if i=='control':control.append(r['goal'])
                else:positive.append(i)
            if i!='control':
                prior=processed[i].get(k)
                if prior is None or prior['status']=='UNKNOWN':processed[i][k]=r
        check(not certs,'certificate missing trial')
    closed=sorted(i for i,objs in processed.items() if objs.keys()==expected[i] and all(r['status'] in ('DUAL','EXHAUSTED','EMPTY') for r in objs.values()))
    unique=Counter(r['status'] for objs in processed.values() for r in objs.values())
    print(json.dumps(dict(original_survivors=len(bank),donors_touched=len(processed),unique_branches=sum(unique.values()),status_ignoring_controls=unique,
        integer_certificates_replayed=replayed,closed_donors=closed,surviving_donors=len(bank)-len(closed),positive=positive,control_lengths=control),indent=2))
if __name__=='__main__':main()
