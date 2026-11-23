from pathlib import Path
from collections import Counter
import json,math
D=Path(__file__).resolve().parent
def rows(name):
    return [json.loads(l) for l in (D/name).read_text().splitlines()]
def path_ok(p):
    assert len(set(p))==len(p) and all(isinstance(x,int) and 0<=x<512 for x in p)
    for j,y in enumerate(p):
        for i,x in enumerate(p[:j]):assert ((x^y).bit_count()==1)==(i+1==j)
def coverage(first,repeat,key,expect,total):
    a={};b={}
    for name,dic in [(first,a),(repeat,b)]:
        data=rows(name);assert data[-1].get('done') is True
        for r in data[:-1]:
            ident=key(r);assert ident not in dic;dic[ident]=r['status']
    assert len(a)==total and set(a)==expect and set(b)=={k for k,v in a.items() if v=='UNKNOWN'}
    final=a|b;assert set(final.values())=={'UNSAT'}
    return dict(cases=total,first_pass_unsat=sum(v=='UNSAT' for v in a.values()),resolved_on_retry=len(b))
report={}
report['seven']=coverage('two.jsonl','retry_two.jsonl',lambda r:(r['row'],r['partition']),{(i,j) for i in range(7) for j in range(945)},7*945)
report['q8_donor']=coverage('full_donor.jsonl','retry_full.jsonl',lambda r:(r['partition'],r.get('group',r.get('extra'))),{(j,e) for j in range(945) for e in range(5)},945*5)
v=json.loads((D.parent/'q9_explicit_q8_96_plus_94.json').read_text())['vertices'];path_ok(v);assert len(v)==192
report['q8_donor']['edges']=len(v)-1;report['q8_donor']['nominal_insertion_combinations']=192*945*5
nearwords=sorted((D.parent/'q9_via_q10/monotone_near.words').read_text().split())
canonical_seven=[]
for w in nearwords:
    if len(w)!=192:continue
    path=[0]
    for c in w:path.append(path[-1]^(1<<int(c)))
    bad={(i,j) for j,v in enumerate(path) for i,u in enumerate(path[:max(0,j-1)]) if (v^u).bit_count()==1}
    if len(bad)==2:canonical_seven.append(bad)
assert len(canonical_seven)==7
report['one_original_chord']=coverage('remove_one.jsonl','retry_one.jsonl',lambda r:(r['seed'],r['partition'],tuple(r['permit'])),{(i,j,p) for i,cs in enumerate(canonical_seven) for j in range(945) for p in cs},13230)
report['controls']={}
for file,length in [('controls.jsonl',191),('insertion_controls.jsonl',191),('two_controls.jsonl',191),('order_controls.jsonl',190),('end_controls.jsonl',191),('bucket_controls.jsonl',191)]:
    d=rows(file);n=0
    for x in d[1:]:
        p=x.get('path',x.get('witness'));assert (p is not None)==(x['status']=='FOUND')
        if p is not None:assert len(p)-1==length;path_ok(p);n+=1
    report['controls'][file]=dict(small=d[0],recovered=n,total=len(d)-1,length=length)
reports={}
control_files={f.name for f in D.glob('*controls.jsonl')}
report['endpoint_check']=rows('both_controls.jsonl')[-1]
assert report['endpoint_check']['tips_checked']==262 and report['endpoint_check']['possible_extensions']==0
for f in sorted(D.glob('*.jsonl')):
    if f.name in control_files:continue
    lines=f.read_text().splitlines();complete=False;cnt=Counter();hits=[]
    for line in lines:
        if not line.endswith('}'):continue
        r=json.loads(line);complete=r.get('done') is True
        if 'counts' in r:cnt=Counter(r['counts'])
        elif 'status' in r:cnt[r['status']]+=1
        p=r.get('found',r.get('path',r.get('witness')))
        if isinstance(p,list):
            path_ok(p)
            if len(p)>=193:hits.append(len(p)-1)
    reports[f.name]=dict(done=complete,counts=dict(cnt),verified_hits=hits)
report['snapshot']=reports
print(json.dumps(report,indent=2))
