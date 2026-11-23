from pathlib import Path
import gzip,json
D=Path(__file__).resolve().parent
def normalize(w):
    d={};return ''.join(d.setdefault(c,str(len(d))) for c in w)
def make():
    mothers=[('near',int(z[1]),list(map(int,z[2:]))) for l in (D.parent/'q9_via_q10/seven_donors.pts').open() if (z:=l.split())[0]=='SEED']
    with gzip.open(D.parent/'q9_port_followup_public191.txt.gz','rt') as f:mothers.extend(('public',i,list(map(int,l.split()))) for i,l in enumerate(f))
    bank={}
    for src,id,p in mothers:
        word=''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:]))
        assert len(set(p))==len(p) and all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
        defects=[(i,j) for j,b in enumerate(p) for i,a in enumerate(p[:max(0,j-1)]) if (a^b).bit_count()==1]
        assert len(defects)==(2 if src=='near' else 0)
        for n in range(93,101):
            stop=len(word)-n
            starts=range(stop+1) if src=='near' else {0,1,2,stop,stop-1,stop-2,stop//2,(stop+1)//2}
            for off in starts:
                if any(off<=i<j<=off+n for i,j in defects):continue
                w=word[off:off+n];u=normalize(w);v=normalize(w[::-1]);k=min(u,v)
                bank.setdefault(k,[src,id,off,u>v])
    records=sorted(bank.items(),key=lambda x:(x[1][0]!='near',x[0]))
    (D/'sources.txt').write_text(''.join(w+'\n' for w,z in records))
    (D/'provenance.json').write_text(json.dumps([z for w,z in records]))
    print('arms',len(bank),'near',sum(z[0]=='near' for w,z in records))
if __name__=='__main__':make()
