from pathlib import Path
import collections,gzip,hashlib,itertools,json,math
D=Path(__file__).resolve().parent;R=D.parent
def cells(w):
    z=[0]
    for d in w:z.append(z[-1]^1<<d)
    return z
def reads(f,d):
    out=[]
    for l in f.read_text().splitlines():
        h,*z=map(int,l.split())
        if h==d:out.append(z)
    return out
def wof(p):return [(x^y).bit_length()-1 for x,y in zip(p,p[1:])]
def check(p,d):
    assert p and all(0<=v<1<<d for v in p)
    for i,j in itertools.combinations(range(len(p)),2):
        h=(p[i]^p[j]).bit_count()
        assert h>0 and (h==1)==(j==i+1)
    return len(p)*(len(p)-1)//2
def valid(p):
    seen=set()
    for i,v in enumerate(p):
        if v in seen or sum((v^1<<k) in seen for k in range(10))!=(i>0):return False
        seen.add(v)
    return True
def complete_map(s,t):
    m={};assert len(s)==len(t)
    for a,b in zip(s,t):
        if a in m:assert m[a]==b
        m[a]=b
    unused=set(range(9))-set(m.values());ins=set(range(10))-set(m)
    for a,b in zip(sorted(ins),sorted(unused)):m[a]=b
    for a in range(10):
        if a not in m:m[a]=0
    assert len(m)==10 and set(m.values())==set(range(9));counts=sorted(collections.Counter(m.values()).values());assert counts==[1]*8+[2]
    return [m[i] for i in range(10)]
def hits(f,source):
    out=[];pairs=0
    for l in f.read_text().splitlines():
        if not l.startswith('HIT '):continue
        _,row,start,a,b,g,w,*z=l.split();row,start,a,b,g=map(int,(row,start,a,b,g));p=list(map(int,z));assert g+1==len(p) and wof(p)==[ord(c)-65 for c in w];pairs+=check(p,9)
        seed=wof(source[row])[start:start+g];target=wof(p);cuts=(0,a,a+b,g);maps=[complete_map(seed[i:j],target[i:j]) for i,j in zip(cuts,cuts[1:])]
        assert cells([maps[k][x] for k,(i,j) in enumerate(zip(cuts,cuts[1:])) for x in seed[i:j]])==p
        out.append(dict(row=row,start=start,edges=g,lengths=[a,b,g-a-b],maps=maps,path=p))
    return out,pairs
def main():
 donors=reads(D/'q10_12.txt',10);ctl=reads(D/'strong_control.txt',10);assert len(donors)==12 and all(len(p)==380 for p in donors)
 source_pairs=sum(check(p,10) for p in donors);cp=sum(check(p,10) for p in ctl);assert len(ctl)==24 and all(len(p)==192 for p in ctl)
 fail=0
 for p in ctl:
    w=wof(p)
    for a,b in itertools.combinations(range(10),2):
        assert not valid(cells([a if x==b else x for x in w]));fail+=1
 controls,pairs=hits(D/'strong_control.log',ctl);assert {r['row'] for r in controls if r['lengths']==[64,64,63]}==set(range(24))
 real,_=hits(D/'real_190.log',donors);assert len(real)==1
 separately,individual_pairs=hits(D/"each190_witness.log",donors);assert len(separately)==12 and {v["row"] for v in separately}==set(range(12))
 scrambled=0
 for line in (D/"scramble.log").read_text().splitlines():
    if not line.startswith("S "):continue
    _,_,a,b,c,w=line.split();cw=lambda s:[ord(t)-65 for t in s];assert not valid(cells(cw(a+b+c)));check(cells(cw(w)),9)
    src=a+b+c
    for x,y in [(0,64),(64,128),(128,191)]:
        A=cw(src[x:y]);B=cw(w[x:y]);m=dict(zip(A,B));assert len(set(m.values()))==len(m) and [m[t] for t in A]==B
    scrambled+=1
 assert scrambled==24
 strict_ctrl=(D/"strict_control.log").read_text().splitlines();assert len(strict_ctrl)==24 and all(l.split()[1]=="HIT" and int(l.split()[2])==int(l.split()[0]) for l in strict_ctrl)
 logs={}
 for f in D.glob('*.log'):
    ls=f.read_text().splitlines()
    if ls and ls[-1].startswith('DONE'):logs[f.name]=ls[-1]
 for g in (192,195,196):
    cutpairs=sum(32<=g-a-b<=112 for a in range(32,113,4) for b in range(32,113,4));want=12*(380-g)*cutpairs;assert int(logs[f'grid_{g}.log'].split()[2])==want
 assert int(logs['allcuts_192.log'].split()[2])==12*4*math.comb(191,2)
 for g in (191,192,195,196):
    if f'full{g}.log' in logs:
        assert int(logs[f'full{g}.log'].split()[2])==12*(380-g)*math.comb(g-1,2)
 out=dict(individual_190=separately,individual_pair_checks=individual_pairs,independently_scrambled_controls=scrambled,controls_impossible_with_one_seam=len(strict_ctrl),frozen_sha256=hashlib.sha256((D/'q10_12.txt').read_bytes()).hexdigest(),d10_source_lines=12,input_sha256=hashlib.sha256((R/'q9_via_q10/donors.txt').read_bytes()).hexdigest(),source_pairs=source_pairs,positive_donors=len(ctl),positive_source_pairs=cp,single_fold_controls_excluded=fail,positive_outputs=len(controls),positive_output_pairs=pairs,known_split_recovered=24,real_witness=real[0],logs=logs)
 if 'replay191.log' in logs:assert int(logs['replay191.log'].split()[2])==12*(380-191)*math.comb(190,2)
 if "strict190.log" in logs:
    a=logs["strict190.log"].split();assert [int(a[i]) for i in [2,4,6]]==[12,2268,2268*math.comb(189,2)]
    assert all(set(wof(p)[:190])==set(range(9)) and valid(p[:191]) for p in donors)
    out["only_190_windows"]=[[i,0] for i in range(12)]
 (D/'verified.json').write_text(json.dumps(out,indent=2)+'\n');print(source_pairs,fail,len(controls),pairs,real[0]['lengths'])
if __name__=='__main__':main()
