from generate import D,R,words,norm,defects,pg,pts
from itertools import combinations,permutations
from collections import defaultdict,Counter
import random,json,sys
def normalized(s):
    t={}
    return ''.join(str(t.setdefault(c,len(t))) for c in s)
def partitions():
    for g in combinations(range(9),3):
        if g[0]:continue
        left=set(range(9))-set(g)
        for h in combinations(sorted(left),3):
            if h[0]!=min(left):continue
            f=sorted(left-set(h));yield ''.join(str(0 if j in g else 1 if j in h else 2) for j in range(9))
def labels(w,g):return ''.join(g[int(x)] for x in w)
def proj(w,dims):return ''.join(x for x in w if x in dims)
def ckey(w):return min(normalized(w),normalized(w[::-1]))
def main():
    mode=sys.argv[1];seed=int(sys.argv[2]);take=int(sys.argv[3]);tries=int(sys.argv[4]);rn=random.Random(seed)
    ids=list(range(len(words)));index=defaultdict(list)
    for i,w in enumerate(words):
        for subset in combinations('012345678',3):
            sub=proj(w,subset)
            for rev,u in ((0,sub),(1,sub[::-1])):
                index[normalized(u)].append((i,rev,''.join(subset),''.join(dict.fromkeys(u))))
    all_label={ckey(labels(w,g)) for w in words for g in partitions()}
    near=(R/'q9_three_axis.in').read_text().split()
    if mode=='control':near=words
    else:near=[w for w in near if len(w)==192 and defects(w)<=2]
    manifest=[];seen=set();counts=Counter()
    for _ in range(tries):
        i=rn.randrange(len(near));w=near[i];gm=''.join(map(str,pg(rn)));sched=labels(w,gm)
        parts=[''.join(x for x in w if gm[int(x)]==str(g)) for g in range(3)]
        options=[]
        for g,s in enumerate(parts):
            ds=list(range(len(s)-1));rn.shuffle(ds)
            variants=[s]
            if mode!='control':
                for k in ds[:18]:
                    if s[k]!=s[k+1]:variants.append(s[:k]+s[k+1]+s[k]+s[k+2:])
            vals=[]
            for h,v in enumerate(variants):
                matches=index.get(normalized(v))
                if not matches:continue
                match=rn.sample(matches,min(12,len(matches)))
                for b,rev,axes,order in match:
                    if mode=='control' and b==i:continue
                    maps=dict(zip(order,dict.fromkeys(v)))
                    vals.append(dict(b=b,rev=rev,axes=axes,mapping=''.join(maps.get(a,'-') for a in axes),track=v,altered=v!=s))
            if not vals:break
            options.append(vals)
        if len(options)!=3:continue
        counts['all_three_regions']+=1
        for rep in range(3):
            choice=[rn.choice(z) for z in options]
            if len({c['b'] for c in choice})<2:continue
            kk=sched
            if mode=='control':
                ys=list(kk);used=[]
                for h in range(rn.randint(2,5)):
                    pos=rn.randrange(1,len(ys)-1)
                    if pos in used or ys[pos]==ys[pos+1]:continue
                    ys[pos],ys[pos+1]=ys[pos+1],ys[pos];used.append(pos)
                kk=''.join(ys)
                if ckey(kk) in all_label:continue
            streams=[iter(v['track']) for v in choice];raw=''.join(next(streams[int(k)]) for k in kk)
            z=(gm,raw)
            if z in seen:continue
            seen.add(z);cost=defects(raw)
            if cost>5 or not cost:continue
            if mode!='control':
                # Every possible one-step deletion is compared to every archived grouping, including reversal.
                can=any(ckey(kk[:j]+kk[j+1:]) in all_label for j in range(len(kk)) if j==0 or kk[j]!=kk[j-1])
                if can:counts['single_insert']=counts.get('single_insert',0)+1
            else:can=False
            manifest.append(dict(template=i,raw=raw,template_word=w,groups=gm,providers=choice,defects=cost,single_insert=can))
            if len(manifest)>=take:break
        if len(manifest)>=take:break
    manifest.sort(key=lambda x:(x['single_insert'],x['defects']))
    base=f'complete_{mode}'
    (D/(base+'.jsonl')).write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in manifest))
    with (D/(base+'.in')).open('w') as f:
        for r in manifest:print(r['raw'],r['groups'],18,9,143,9,file=f)
    print('templates',len(near),'unique projected tracks',len(index),'archive_group_patterns',len(all_label),'saved',len(manifest),'costs',Counter(r['defects'] for r in manifest),'strict',sum(not r['single_insert'] for r in manifest),'changed_tracks',sum(any(p['altered'] for p in r['providers']) for r in manifest),counts,flush=True)
if __name__=='__main__':main()
