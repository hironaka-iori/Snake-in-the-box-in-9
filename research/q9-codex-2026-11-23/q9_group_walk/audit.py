from pathlib import Path
from collections import Counter
import json
D=Path(__file__).resolve().parent
def issues(p):
    assert all(0<=v<512 for v in p)
    return [(i,j,(u^v).bit_count()) for j,v in enumerate(p) for i,u in enumerate(p[:j]) if u==v or (((u^v).bit_count()==1)!=(j==i+1))]
def check(p,n):
    assert len(p)==n+1 and not issues(p)
def lines(f):
    with f.open() as stream:
        for raw in stream:
            if raw.endswith('\n'):yield raw.split()
def cyclic_code(p):
    if p[0]==p[-1]:p=p[:-1]
    def normal(w):
        names={};return bytes(names.setdefault(x,len(names)) for x in w)
    z=[u^v for u,v in zip(p,p[1:]+p[:1])]
    assert all(e and e&(e-1)==0 for e in z)
    return min(normal(w[i:]+w[:i]) for w in (z,z[::-1]) for i in range(len(w)))
def main():
    out={};long=[]
    for f in [D/'control.log',*(D.glob('archive*.log')),D/'fresh8.log']:
        c=Counter();best=None
        for x in lines(f):
            c[x[6]]+=1;best=min(int(x[4]),best if best is not None else 9999)
            if x[6]=='FOUND':
                p=list(map(int,x[9:]));check(p,int(x[2]))
                if len(p)>=193:long.append(p)
        out[f.stem]=dict(counts=c,min_defects=best)
    for f in [D/'cross_control.log',*D.glob('cross[0-9]*.log')]:
        x=list(lines(f));out[f.stem]=dict(bank=x[0][1:],last_count=next((r for r in x[::-1] if r[0] in ('DONE','CHECK')),None))
        for r in x:
            if r[0]=='FOUND':
                p=list(map(int,r[1:]));check(p,191 if 'control' in f.name else 192);out[f.stem]['checked_edges']=len(p)-1
                if len(p)>=193:long.append(p)
    for f in [D/'seam_control.log',D/'seam2.log',D/'seam8.log']:
        rows=0;found=0;cuts=0;places=0
        for r in lines(f):
            if r[0]=='ROW':rows+=1;cuts+=int(r[3]);places+=int(r[5])
            if r[0]=='FOUND':
                q=list(map(int,r[6:]));check(q,int(r[2]));found+=1
                if len(q)>=193:long.append(q)
        out[f.stem]=dict(rows=rows,found=found,cuts=cuts,placements=places)
    for f in [*D.glob('color*.jsonl'),*D.glob('half*.jsonl'),D/'interior.jsonl']:
        c=Counter()
        for r in lines(f):
            v=json.loads(' '.join(r));c[v['status']]+=1
            if v['vertices']:
                q=v['vertices'];check(q,191 if 'control' in f.name else 192)
                if len(q)>=193:long.append(q)
        out[f.stem]=c
    for f in D.glob('rotate*.log'):
        n=Counter()
        for r in lines(f):
            if r[0]=='BANK':
                n[int(r[3])]+=1
            elif r[0]=='FOUND':
                q=list(map(int,r[3:]));check(q,int(r[2]));long.append(q)
        out[f.stem]=dict(recorded_bank_defects=n)
    near=[]
    for f in list(D.glob('common*.log'))+list(D.glob('hybrid*.log')):
        c=Counter()
        for r in lines(f):
            if r[0] in ('NEAR','FOUND'):
                p=list(map(int,r[2:]));b=issues(p);assert len(p)==193 and len(b)==int(r[1])
                assert all(i>=5 and j<len(p)-5 and h==1 and j>i+1 for i,j,h in b)
                c[len(b)]+=1
                if b:near.append(dict(source=f.name,defects=b,vertices=p))
                else:long.append(p)
        out[f.stem]=c
    ref=json.loads((D.parent/'q9_coil_open_191_witness.json').read_text())['cycle']
    for r in lines(D.parent/'q9_two_cross_lower_tips_20261121/soft.log'):
        if r[0]!='NEAR':continue
        n,m,*v=map(int,r[5:]);a,b=v[:n],v[n:];q=a[::-1]+[v+256 for v in b]+[b[-1]]
        if q[-1]!=q[0] or len(set(q))!=len(q)-1:continue
        assert issues(q[:-1])==[(0,len(q)-2,1)]
        out['same_as_reference_cycle']=cyclic_code(q)==cyclic_code(ref)
    out['direct_small_checks']=(D/'small_check.log').read_text().strip()
    out['bounded_small_checks']=(D/'check_bounded.log').read_text().strip()
    out['hybrid_near_examples']=sorted(near,key=lambda r:len(r['defects']))[:4]
    out['long_paths']=long
    (D/'verified.json').write_text(json.dumps(out,indent=2)+'\n')
    print('independently checked long paths',len(long),'interior hybrids',len(near))
if __name__=='__main__':main()
