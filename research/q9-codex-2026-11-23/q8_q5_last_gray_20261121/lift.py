import json
from collections import Counter
def enumerate_words(x,mask,w):
    if len(w)==15:yield w
    for d in range(4):
        y=x^(1<<d)
        if not ((mask>>y)&1):
            yield from enumerate_words(y,mask|(1<<y),w+(d,))
def canon(w):
    def rename(x):
        seen={}
        return tuple(seen.setdefault(d,len(seen)) for d in x)
    return min(rename(w),rename(w[::-1]))
last=canon((0,1,2,1,0,1,2))
words=list(enumerate_words(0,1,()))
by=Counter();classes={}
for w in words:
    if len(set(w[:7]))==len(set(w[8:]))==3:
        k=int(canon(w[:7])==last)+int(canon(w[8:])==last)
        by[k]+=1
        assert classes.setdefault(canon(w),k)==k
print(json.dumps(dict(rooted=len(words),all_classes=len(set(map(canon,words))),rooted_by_last_halves=by,classes_by_last_halves=Counter(classes.values())),indent=2))
