from pathlib import Path
D=Path(__file__).resolve().parent;b={}
for l in (D.parent/'each.paths').read_text().splitlines():
    n,k,*p=map(int,l.split())
    if n!=189:continue
    w=''.join(str((u^v).bit_length()-1) for u,v in zip(p,p[1:]));a,m,c=w.split('8');b[k]=(m,a[::-1],c)
assert set(b)=={0,1}
(D/'donors.words').write_text('\n'.join(b[i][0] for i in sorted(b))+'\n');(D/'direct.dat').write_text('\n'.join(' '.join([str(i),*b[i][1:]]) for i in sorted(b))+'\n')
