import argparse,json,itertools
from pathlib import Path
from collections import Counter
D=Path(__file__).resolve().parent
def load(f):return {r['id']:r for l in (D/(f+'.jsonl')).read_text().splitlines() if (r:=json.loads(l))}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--solve',type=int);ap.add_argument('--prior');a=ap.parse_args()
    first=load('allpairs_atleast');second=load('independent_wide');old=load(a.prior) if a.prior else {}
    if a.solve:
        from octsolve import bank,split,solve,cube
        for i in sorted(first.keys()&second.keys()):
            if i in old or first[i]['status']!='UNKNOWN' or second[i]['status']!='UNKNOWN':continue
            r=first[i];p=bank[r['source']];axes=r['axes'];us=[split(cube,d)-split(p,d) for d in axes]
            ans=solve(p,axes,us,193,a.solve,require_new=False);ans.update(id=i,source=r['source'],axes=axes)
            print(json.dumps(ans),flush=True)
    else:
        assert len(first)==len(second)==288
        retry=load('wide_retry');assert set(retry)=={i for i in first if first[i]['status']==second[i]['status']=='UNKNOWN'}
        total={};agreement=Counter()
        for i in first:
            assert first[i]['axes']==second[i]['axes'] and first[i]['source']==second[i]['source']
            vals=[first[i]['status'],second[i]['status']]
            if i in retry:vals.append(retry[i]['status'])
            assert 'FOUND' not in vals
            total[i]='UNSAT' if 'UNSAT'in vals else 'UNKNOWN';agreement[tuple(vals[:2])]+=1
        sums=lambda v:dict(Counter(x['status'] for x in v.values()))
        summary=dict(jobs=len(total),native=sums(first),independent=sums(second),joint_retry=sums(retry),final=dict(Counter(total.values())),by_source={str(k):dict(Counter(total[i] for i in total if first[i]['source']==k)) for k in sorted({x['source'] for x in first.values()})},initial_agreement={'+'.join(k):n for k,n in sorted(agreement.items())},small_atleast=json.loads((D/'small_atleast.json').read_text()),single_open=sums(load('single_open')))
        print(json.dumps(summary,indent=2))
