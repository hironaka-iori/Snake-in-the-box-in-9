"""Pairwise validation of controls and independent exhaustive reassembly of saved instances."""
import json,itertools
from functools import lru_cache
from pathlib import Path
here=Path(__file__).resolve().parent
def vertices(w):
    p=[0]
    for d in w:p.append(p[-1]^(1<<d))
    return p
def valid(p):
    return len(set(p))==len(p) and all(0<=v<512 for v in p) and all(((v^u).bit_count()==1)==(i+1==j) for (i,v),(j,u) in itertools.combinations(enumerate(p),2))
def split(w,d):
    s=''.join(map(str,w));chunks=s.split(str(d));blocks=[list(map(int,u)) for u in chunks]
    starts=[0]
    for b in blocks[:-1]:starts.append(starts[-1]+len(b)+1)
    return starts,blocks
def fitted(w,p,d):
    scores=[[0]*9 for _ in range(9)]
    for a,b in zip(w,w[p:]):
        if d not in (a,b):scores[a][b]+=1
    dp=[-1]*512;last=[0]*512;dp[0]=0
    for m in range(511):
        if dp[m]<0:continue
        a=m.bit_count()
        for b in range(9):
            if m>>b&1 or (a==d)!=(b==d):continue
            n=m|1<<b;v=dp[m]+scores[a][b]
            if v>dp[n]:dp[n]=v;last[n]=b
    perm=[0]*9;m=511
    for i in reversed(range(9)):perm[i]=last[m];m^=1<<perm[i]
    return perm
def option(w,sep,p,starts,blocks,perm,j,source,offset,length,power,flip):
    inv=[perm.index(k) for k in range(9)];out=blocks[j].copy()
    if source>=0:
        assert abs(source-starts[j]-offset)==p and length in (1,2,3,5,8)
        repl=w[source:source+length];assert len(repl)==length and sep not in repl
        trans=perm if source<starts[j]+offset else inv
        out[offset:offset+length]=[trans[d] for d in repl]
    if power:out=[(perm if power==1 else inv)[d] for d in out]
    return out[::-1] if flip else out
def control(name,known):
    lines=(here/(name+'.log')).read_text().splitlines();h=lines[0].split();row=int(h[2]);sep=int(h[6]);p=int(h[8]);w=list(map(int,h[10]));reported=list(map(int,h[12:]))
    assert not valid(vertices(w)) and valid(vertices(known[row]))
    perm=fitted(w,p,sep);assert perm==reported
    starts,blocks=split(w,sep);used=[];out=[];borrowed=0
    for l in lines[1:-1]:
        k=l.split();j,src,at,n,pow_,rev=map(int,[k[1],k[3],k[5],k[7],k[9],k[11]])
        u=option(w,sep,p,starts,blocks,perm,j,src,at,n,pow_,rev);assert u==list(map(int,k[13])) and valid(vertices(u))
        if used:out.append(sep)
        out.extend(u);used.append(j);borrowed+=src>=0
    witness=list(map(int,lines[-1].split()[1:]));assert len(witness)==192 and valid(witness) and witness==vertices(out) and sorted(used)==list(range(len(blocks)))
    if name.endswith('order'):assert used!=sorted(used)
    else:assert borrowed
    return {'edges':len(out),'period':p,'reordered_blocks':used,'borrowed':borrowed}
def independent(case,rows):
    id,row,sep,p,n,was_sat,_=case[0];w=rows[row];starts,blocks=split(w,sep);perm=fitted(w,p,sep)
    assert n==len(blocks);opts=[[] for _ in blocks]
    for opt in case[1:]:
        j,src,off,le,po,r=opt[:6];u=list(map(int,opt[6]))
        assert u==option(w,sep,p,starts,blocks,perm,j,src,off,le,po,r) and valid(vertices(u))
        opts[j].append((tuple(vertices(u)),int(src>=0)))
    ball=[sum(1<<y for y in [x]+[x^(1<<d) for d in range(9)]) for x in range(512)]
    @lru_cache(None)
    def placement(vertices_,origin):
        seq=[u^origin for u in vertices_];bits=sum(1<<v for v in seq);halo=0
        for q in seq:halo|=ball[q]
        return bits,halo,seq[-1]
    def dfs(used,tip,occ,halo,damage):
        if used.bit_count()==n:return True
        anchor=tip^(1<<sep) if used else 0
        if used and ((occ>>anchor)&1 or (occ&ball[anchor]).bit_count()!=1):return False
        for j,vs in enumerate(opts):
            if used>>j&1:continue
            for v,k in vs:
                if k>damage:continue
                bits,h,end=placement(v,anchor)
                if used and (bits^(1<<anchor))&halo:continue
                if dfs(used|1<<j,end,occ|bits,halo|h,damage-k):return True
        return False
    ans=dfs(0,0,0,0,2);assert ans==bool(was_sat);return ans
def main():
    known=[list(map(int,w)) for w in (here.parent/'q9_gap_generations/prior191.words').read_text().splitlines()]
    bank=[list(map(int,w)) for w in (here.parent/'q9_three_axis.in').read_text().splitlines()]
    result={name:control(name,known) for name in ('control-order','control-period')}
    cases=[]
    for l in (here/'instances.txt').read_text().splitlines():
        x=l.split()
        if x[0]=='CASE':cases.append([list(map(int,x[1:]))])
        else:cases[-1].append([*map(int,x[1:7]),x[7]])
    assert len(cases)==48;result['finite_templates']={'count':len(cases),'solutions':sum(independent(c,bank) for c in cases)}
    for f in sorted(here.glob('flex*.log')):
        lines=f.read_text().splitlines();assert lines[-1].startswith('DONE ')
        for i,l in enumerate(lines):
            if l.startswith('FREE_WITNESS'):
                n=int(l.split()[1]);seq=list(map(int,lines[i+1].split()[1:]));assert n==len(seq)-1 and valid(seq)
        result[f.stem]=[l for l in lines if l.startswith(('FREE_WITNESS','ENDS','DONE'))]
    for f in sorted(here.glob('res*.log')):
        lines=f.read_text().splitlines()
        if lines[0].startswith('REC '):
            rec=lines[0].split();row,period,sep,maximum=map(int,rec[1:5]);w=list(map(int,rec[5]))
            tracks=list(map(int,lines[1].split()[1:]));perm=list(map(int,lines[2].split()[1:]));output=list(map(int,lines[3].split()[1:]))
            assert valid(output) and perm==fitted(w,period,sep)
            if 'control' in f.name:assert not valid(vertices(w)) and sum(x!=y for x,y in zip(w,known[row]))==1
            else:assert w==bank[row]
            new=[(x^y).bit_length()-1 for x,y in zip(output,output[1:])]
            assert len(new)==len(w) and all(y==x for i,(x,y) in enumerate(zip(w,new)) if i%period not in tracks)
            violations=[sum(perm[x]!=y for x,y in zip(new[r::period],new[r+period::period])) for r in tracks]
            assert all(z<=maximum for z in violations)
            result[f.stem]=dict(edges=len(new),period=period,residues=tracks,exceptions=violations)
        else:assert lines[-1].startswith('DONE ');result[f.stem]=lines[-1]
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
