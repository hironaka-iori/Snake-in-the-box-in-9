"""Enumerate exact small vertex trades from newly verified 189-edge seeds."""
import gzip,json,math,re,subprocess,sys
from pathlib import Path
from collections import Counter
D=Path(__file__).resolve().parent
R=D.parent
def points(w):
    p=[0]
    for d in w:p.append(p[-1]^1<<int(d))
    return p
def validate(p):
    assert len(p)==len(set(p)) and all(0<=v<512 for v in p)
    assert all(((v^u).bit_count()==1)==(i==j+1) for i,v in enumerate(p) for j,u in enumerate(p[:i]))
def canon(w):
    def norm(s):
        labels={};return ''.join(str(labels.setdefault(x,len(labels))) for x in s)
    return min(norm(w),norm(w[::-1]))
def collect():
    seeds=(R/"q9_fresh189_multirewire_20261121/new189.words").read_text().split()
    bank=set()
    for f in json.loads((R/"q9_fresh189_multirewire_20261121/bank_files.json").read_text()):
        p=R/f
        body=gzip.open(p,"rb").read() if f.endswith(".gz") else p.read_bytes()
        for w in set(body.split()):
            if re.fullmatch(rb"[0-8]{190,191}",w):bank.update(canon(w[i:i+190].decode()) for i in range(len(w)-189))
    parents=[points(w) for w in seeds]
    for p in parents:validate(p)
    inp=''.join(' '.join(map(str,p))+'\n' for p in parents)
    all_found={};counts=[]
    for k in [1,2,3,4]:
        proc=subprocess.run([str(D/"trades"),"9",str(k),"--all-fast=1"],input=inp,text=True,capture_output=True,check=True)
        rows=0;hits=0
        for line in proc.stdout.splitlines():
            fields=line.split()
            if fields[0]=="PATH":
                p=list(map(int,fields[1:]));validate(p);assert len(p)==191 and len(set(parents[rows])-set(p))==k
                w=canon(''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:])))
                all_found.setdefault(w,[rows,k]);hits+=1
            else:
                assert int(fields[0])==rows and int(fields[2])==math.comb(190,k)
                rows+=1
        assert rows==len(parents)
        counts.append([k,hits]);fresh=sorted(set(all_found)-bank)
        (D/"novel190.words").write_text(''.join(x+'\n' for x in fresh))
        (D/"offspring.json").write_text(json.dumps(dict(seeds=len(seeds),bank=len(bank),counts=counts,distinct=len(all_found),fresh={w:all_found[w] for w in fresh}),indent=2))
        print(k,hits,len(all_found),len(fresh),flush=True)
if __name__=="__main__":collect()
