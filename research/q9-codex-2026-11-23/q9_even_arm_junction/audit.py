from pathlib import Path
import json,gzip,math,collections,hashlib
from bank import valid,canon
D=Path(__file__).resolve().parent;R=D.parent
def key(p):
 w=''.join(str((u^v).bit_length()-1) for u,v in zip(p,p[1:]))
 def norm(z):
    t={};return ''.join(str(t.setdefault(c,len(t))) for c in z)
 return min(norm(w),norm(w[::-1]))
def masks(p):return [x^y for x,y in zip(p[::2],p[2::2])]
def permute(m,img):
    v=0
    for x in range(9):
        if m>>x&1:assert 0<=img[x]<9;v^=1<<img[x]
    return v
def states(files):
    out=[]
    for f in files:
        for l in f.read_text().splitlines():
            if not l.startswith('DONE '):continue
            z=l.split()[1:]
            if len(z)%2:continue
            out.append(dict(file=f.name,**{z[i]:int(z[i+1]) for i in range(0,len(z),2)}))
    return out
def validate_logs(logs,arms):
    records={};pairs=0;copies=0
    for f in logs:
      for l in f.read_text().splitlines():
        if not l.startswith('W '):continue
        n,i,j,depth,lo,hi,*extra=map(int,l.split()[1:]);image,p=extra[:9],extra[9:];assert len(p)==n+1 and valid(p)
        seen=[a for a in image if a>=0];assert len(seen)==len(set(seen))
        z=p[lo>=0:len(p)-(hi>=0)];assert z[0]==0 and len(z)==97+2*depth
        expect=arms[i][::-1]+[permute(d,image) for d in arms[j][:depth]]
        assert masks(z)==expect
        k=key(p);records.setdefault(k,dict(source=f.name,length=n,left=i,right=j,retained_right_steps=2*depth,odd_tips=[lo,hi],image=image,path=p));copies+=1;pairs+=n*(n+1)//2
    return records,copies,pairs
def main():
    arms=[list(map(int,l.split())) for l in (D/'arms.txt').read_text().splitlines()]
    prov=json.loads((D/'provenance.json').read_text());assert len(arms)==len(prov)==17793 and len(set(map(tuple,arms)))==len(arms)
    hist=collections.Counter(k for r in prov for k in r);fs=sorted(D.glob('full_*.log'));rows=states(fs);assert sum(z['rows'] for z in rows)==len(arms) and all(not z['capped'] for z in rows)
    paths,entries,np=validate_logs(fs,arms);public=[list(map(int,l.split())) for l in gzip.open(R/'q9_port_followup_public191.txt.gz','rt')];known={key(p) for p in public};ctl=json.loads((D/'controls.json').read_text());checked=0
    for item in ctl:
        for side in ("l","r"):
            pts=[0]
            for ax in item[side]:pts.append(pts[-1]^1<<ax)
            assert valid(pts)
    for l in (D/'control.log').read_text().splitlines():
        if not l.startswith('CONTROL '):continue
        i,n,*p=map(int,l.split()[1:]);assert n==190 and valid(p) and len(p)==191
        q=ctl[i];blocks=[]
        for nm in ['l','r']:
            s=q[nm];blocks.append([(1<<u)|(1<<v) for u,v in zip(s[::2],s[1::2])])
        assert masks(p)[:48]==blocks[0][::-1] and canon(masks(p)[48:])==canon(blocks[1]);checked+=1
    assert checked==len(ctl)==32
    for tag in ['independent_control','port_control']:
        cc=[l for l in (D/(tag+'.log')).read_text().splitlines() if l.startswith('JOIN ')];assert len(cc)==32
        for l in cc:
            p=list(map(int,l.split()[(5 if tag=='independent_control' else 13):]));assert len(p)==191 and valid(p)
    summary=dict(source_arms=hist,union=len(arms),pair_count=len(arms)*(len(arms)+1)//2,ordered_search=rows,canonical_lengths=dict(collections.Counter(map(len,paths))),known191=sum(len(k)==191 and k in known for k in paths),verified_output_rows=entries,verified_pairs=np,strong_controls=checked,changed_original_odd_range=[min(q['changed_left']+q['changed_right'] for q in ctl),max(q['changed_left']+q['changed_right'] for q in ctl)],best=paths[max(paths,key=len)],relaxed=states([D/'relaxed.log',D/'portsample.log',*sorted(D.glob('port_exact*.log'))]),arm_sha256=hashlib.sha256((D/'arms.txt').read_bytes()).hexdigest())
    if (D/'combined_arms.txt').exists():
        a2=[list(map(int,l.split())) for l in (D/'combined_arms.txt').read_text().splitlines()];ff=sorted(D.glob('alt_join_*.log'));res=states(ff)
        if ff and len(res)==len(ff):
            ws,nc,npa=validate_logs(ff,a2);summary['alternate_orders']=dict(combined=len(a2),search=res,lengths=dict(collections.Counter(map(len,ws))),outputs=nc,checked_pairs=npa)
    summary["state_prefix_validation"]=(D/"state_check.log").read_text().strip()
    summary["fixed_odd_full_permutation_control"]=(D/"rigid_check.log").read_text().strip()
    summary["order_generator"]=(D/"alternate_source.log").read_text().splitlines()[-1]
    (D/'verified.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary['canonical_lengths'],summary['known191'],np)
if __name__=='__main__':main()
