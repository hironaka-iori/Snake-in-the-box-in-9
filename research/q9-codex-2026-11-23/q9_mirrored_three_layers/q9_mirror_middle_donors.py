import itertools,collections,sys
def canon(word):
    tr={};return ''.join(tr.setdefault(x,str(len(tr))) for x in word)
def add(p):
    if len(set(p))>7:return
    q=canon(p);bank.add(min(q,canon(q[::-1])))
bank=set()
for row in open('/private/tmp/q7_quad_short20.txt'):
    _,*p=map(int,row.split());add(''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:])))
old=set(bank)
maximal=set()
for line in itertools.chain(open('q8_single_cross_complete_arms.txt'),open('q8_coils_reconstructed.txt')):
    s=line.strip()
    for i in range(len(s)-33):
        p=s[i:i+51]
        if len(set(p[:33]))>7:continue
        for j in range(33,len(p)+1):
            if len(set(p[:j]))>7:break
            if j==len(p) or p[j] not in p[:j] and len(set(p[:j]))==7:
                maximal.add(canon(p[:j]))
for p in maximal:
    for n in range(33,len(p)+1):
        add(p[:n]);add(p[-n:])
for s in sorted(bank-old,key=lambda s:(-len(s),s)):
    v=[0]
    for c in s:v.append(v[-1]^(1<<int(c)))
    print(len(v),*v)
print(collections.Counter(map(len,bank-old)),file=sys.stderr)
