from pathlib import Path
D=Path(__file__).resolve().parent;seen=set();out=[]
def key(p,s):
    options=[]
    for q in (p,p[::-1]):
        ds=list(dict.fromkeys((u^v).bit_length()-1 for u,v in zip(q,q[1:])));assert len(ds)==8
        conv=lambda x:sum(((x^q[0])>>d&1)<<k for k,d in enumerate(ds))
        options.append((tuple(map(conv,q)),tuple(sorted(map(conv,s)))))
    return min(options)
for original in (0,1):
    for row in (D/f'splice93_{original}.dat').read_text().splitlines():
        i,rev,lo,hi,n,*v=map(int,row.split());p=v[:n];s=v[n+1:];k=key(p,s)
        if k in seen:continue
        seen.add(k);out.append(row)
(D/'check93.dat').write_text('\n'.join(out)+'\n');print('distinct geometries',len(out))
