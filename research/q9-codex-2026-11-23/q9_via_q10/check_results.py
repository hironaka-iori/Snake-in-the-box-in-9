"""Independently check the emitted paths and coverage of case lists."""
from collections import Counter
from pathlib import Path
import gzip
import json
import hashlib
root=Path(__file__).resolve().parent
source=root.parent/'q9_port_highdim_parents.txt.gz'
def valid(path,dim):
    assert len(set(path))==len(path) and all(0<=x<1<<dim for x in path)
    assert all((x^y).bit_count()==1 for x,y in zip(path,path[1:]))
    points=set(path)
    edges=sum((x^(1<<b)) in points for x in points for b in range(dim))//2
    assert edges==len(path)-1
def rows(file):
    return [s.split() for s in (root/file).read_text().splitlines() if s]
donors={}
for s in gzip.open(source,'rt'):
    d,*p=map(int,s.split());valid(p,d);donors.setdefault(d,[]).append(p)
out={'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'fixed':{},'one_free_axis':{}}
for d,bank in donors.items():
    counts={}
    for n in (190,191,192):
        entries=rows(f'kernel_{d}_{n}.log')
        data=[r for r in entries if r[0]=='ROW']
        assert list(map(lambda r:int(r[1]),data))==list(range(len(bank)))
        assert sum(int(r[2]) for r in data)==int(entries[-1][2])
        hits=[r for r in entries if r[0]=='PATH']
        assert len(hits)==sum(int(r[2])>0 for r in data)
        for hit in hits:
            _,r,j,k,*q=hit;p=list(map(int,q));valid(p,9)
            assert len(p)==int(k)+1==n+1
            src=bank[int(r)][int(j):int(j)+n+1]
            mapping={}
            for ax,b in zip((u^v for u,v in zip(src,src[1:])),(u^v for u,v in zip(p,p[1:]))):
                assert mapping.setdefault(ax,b)==b
        counts[n]=int(entries[-1][2])
    out['fixed'][d]=dict(donors=len(bank),edges=len(bank[0])-1,fold_window_counts=counts)
for n in (191,192):
    entries=rows(f'limits_{n}.log')
    cases=[tuple(map(int,r[1:])) for r in entries if r[0]=='LIMIT']
    total,yes,no,unknown,_,_=map(int,entries[-1][1:])
    assert entries[-1][0]=='DONE' and len(cases)==len(set(cases))==unknown
    assert total==len(donors[10])*10*(len(donors[10][0])-n) and yes==0 and total==no+unknown
    retry=rows(f'retry{n}.log');assert len(retry)==unknown
    assert set(tuple(map(int,r[1:4])) for r in retry)==set(cases) and all(r[4]=='0' for r in retry)
    out['one_free_axis'][n]=dict(windows_and_axis_choices=total,first_solver_excluded=no,second_solver_excluded=unknown)
def check_port(src,mask,off,w):
    valid(w,9)
    for j,(a,b) in enumerate(zip(w,w[1:]),off):
        z=src[j]^src[j+1]
        if mask&z:assert a^b==1<<(mask&(z-1)).bit_count()
_,r,off,mask,n,*p=rows('ports_190_witness.log')[0]
q=list(map(int,p));assert len(q)==int(n)+1==191
check_port(donors[10][int(r)],int(mask),int(off),q)
out['one_free_axis']['max']=190
controls=rows('translation_control.log');assert len(controls)==36
parents=[list(map(int,line.split()))[1:] for line in (root/'control_donors.txt').read_text().splitlines()]
for tag,r,m,off,st,nodes,*p in controls:
    assert tag=='CASE' and st=='1' and len(p)==192
    check_port(parents[int(r)],int(m),int(off),list(map(int,p)))
out['translation_controls']=len(controls)
seams=(root/'all_seams_192.log').read_text().splitlines()
out['single_seam_snapshot']={'completed_cut_positions':len(seams),'total_cut_positions':191,
                            'found':sum('FOUND' in line for line in seams)}
print(json.dumps(out,indent=2))
