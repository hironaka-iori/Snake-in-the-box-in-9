"""Verify 9-dimensional excerpts and try every possible sequence of end additions."""
from collections import Counter
from pathlib import Path
import argparse, csv, io, json, zipfile


def canon(word):
    def one(seq):
        m={}
        return bytes(m.setdefault(d,len(m)) for d in seq)
    return min(one(word),one(word[::-1]))


def walk(word):
    p=[0]
    for d in word:p.append(p[-1]^(1<<d))
    return p


def word(p):
    return [(a^b).bit_length()-1 for a,b in zip(p,p[1:])]


def verify(p):
    assert len(set(p))==len(p) and max(p)<512
    assert all(((p[i]^p[j]).bit_count()==1)==(j==i+1) for i in range(len(p)) for j in range(i+1,len(p)))


def extend(p,seen,novel,old,counts):
    c=canon(word(p))
    if c in seen:return None
    seen.add(c)
    counts[len(p)-1]+=1
    if len(p)>=192 and c not in old:
        verify(p);novel[c]=p
    if len(p)>=193:
        verify(p);return p
    occupied=set(p)
    for side in (p,p[::-1]):
        for d in range(9):
            u=side[-1]^(1<<d)
            if u in occupied or sum((u^(1<<k)) in occupied for k in range(9))!=1:continue
            result=extend(side+[u],seen,novel,old,counts)
            if result:return result
    return None


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('zip');ap.add_argument('excerpts')
    args=ap.parse_args()
    with zipfile.ZipFile(args.zip) as z:
        old=set()
        for row in csv.DictReader(io.TextIOWrapper(z.open('record_snakes.csv'))):
            if row['n']!='9':break
            old.add(canon(list(map(int,row['actions'].split()))))
    assert len(old)==131
    source_counts=Counter()
    seen=set();novel={};counts=Counter();result=None
    for line in Path(args.excerpts).read_text().splitlines():
        dim,code,n,row,start,end=line.split()
        if dim!='9':continue
        p=walk([ord(c)-97 for c in code]);verify(p)
        source_counts[(int(n),len(p)-1)]+=1
        result=extend(p,seen,novel,old,counts)
        if result:break
    print(json.dumps({'sources':sorted([list(k)+[v] for k,v in source_counts.items()]),'visited':counts,'new_191_or_more':list(novel.values()),'target':result}))
