"""Pure-Python geometry and source replay for the doubled-step construction."""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import json
D=Path(__file__).resolve().parent
def lines(name):return (D/name).read_text().splitlines()
archive=(D.parent/'q9_gap_generations/prior191.words').read_text().split()
qbank=(D.parent/'q8_catalogue_96_98.words').read_text().split()
@lru_cache(maxsize=100000)
def validate(w):
    v=0;seen=1
    for c in w:
        prev=v;v^=1<<int(c)
        assert not (seen>>v)&1 and (hood[v]&seen)==1<<prev
        seen|=1<<v
def shape(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return sum((x^y).bit_count()<=1 for i,x in enumerate(p) for j,y in enumerate(p[:i]) if j+1<i)
hood=[sum(1<<(x^1<<k) for k in range(9)) for x in range(512)]
for w in archive+qbank:validate(w)
mothers=[]
for i,row in enumerate(lines('mothers.tsv')):
    idx,src,rev,st,w=row.split();orig=qbank[int(src)];orig=orig[::-1] if int(rev) else orig
    assert int(idx)==i and orig[int(st):int(st)+96]==w and len(w)==96
    mothers.append(w)
def seeds(fn):
    rs=[]
    for row in lines(fn):
        d,offset,m,start,ln,sel=row.split();d,offset,m,start,ln=map(int,(d,offset,m,start,ln))
        word=archive[d][offset:offset+2*ln];mother=mothers[m][start:start+ln]
        assert len(sel)==ln==len(mother)==len(word)//2
        iso={}
        for j,(a,b) in enumerate(zip(mother,sel)):
            assert b in word[2*j:2*j+2] and iso.setdefault(a,b)==b
        assert len(set(iso.values()))==len(iso)
        rs.append((d,offset,m,start,ln,sel))
    return rs
best=seeds('best.tsv');sample=seeds('sample.tsv');centers=seeds('centers.tsv')
answer={'archive_geometry':len(archive),'catalogue_geometry':dict(Counter(map(len,qbank))),'oriented_96_windows':len(mothers),'checked_matching_records':len(best)+len(sample)+len(centers),'best_per_Q9_record':dict(Counter(s[4] for s in best))}
examples={'longest_catalogue_match':max(best,key=lambda r:r[4])}
for fn,srs in [('positive',best),('warm',best),('prefix',centers),('suffix',centers)]:
    cnt=Counter();lens=Counter();ids=set();high=0;maxrow=None
    for line in lines(fn+'.tsv'):
        toks=line.split();i,rep,L,H,lo,hi,u,v=map(int,toks[:8]);mp,w=toks[8:];don,offset,mo,st,ln,_=srs[i];mw=mothers[mo]
        assert 0<=L<=u<=lo<hi<=v<=H<=96 and len(w)==2*(v-u) and len(mp)==len(set(mp))==8
        assert all(mp[int(mw[j])] in w[2*(j-u):2*(j-u)+2] for j in range(u,v))
        fixed=archive[don][offset+2*(lo-st):offset+2*(hi-st)]
        assert w[2*(lo-u):2*(hi-u)]==fixed
        validate(w);cnt['outputs']+=1;ids.add((i,rep));lens[len(w)]+=1
        if (u,v)==(L,H):
            cnt['reached_outputs']+=1
            if fn=='positive':
                cnt['released_both_tips']+=(lo>L and hi<H)
                orig=archive[don][offset:offset+2*ln]
                cnt['returned_word_differs_from_donor']+=w!=orig
        if len(w)>high:high=len(w);maxrow=dict(input=i,repetition=rep,donor=don,mother=mo,lo=u,hi=v,mapping=mp,word=w)
    cnt['highest_edges']=high;cnt['distinct_runs']=len(ids);answer[fn]=dict(cnt)
    if fn in ('positive','warm'):examples[fn]=maxrow
for fn in ['free_exact','free']:
    high=0
    for ln in lines(fn+'.records'):
        d,o,k,q8,q9=ln.split();d,o,k=map(int,(d,o,k))
        assert q9==archive[d][o:o+2*k] and len(q8)==k and len(set(q8))<=8 and all(c in q9[2*j:2*j+2] for j,c in enumerate(q8))
        validate(q8);validate(q9)
        if k>high:high=k;rec={'archive_row':d,'offset':o,'pairs':k,'kept_word':q8,'Q9_word':q9}
    answer[fn+'_longest_witness']=high
    if fn=='free_exact':examples['free']=rec
def even_stats(w):
    even=[0];mid=[]
    for i in range(0,len(w),2):
        x=even[-1];a,b=[1<<int(c) for c in w[i:i+2]]
        assert a!=b
        mid.append((x^a,x^b));even.append(x^a^b)
    counts=Counter(even);duplicate=sum(n*(n-1)//2 for n in counts.values())
    def score(x):return sum(counts.get(x^(1<<k),0) for k in range(9))
    costs=[min(score(a),score(b))-2 for a,b in mid]
    return duplicate,sum(s>0 for s in costs),sum(costs)
counts=Counter();min_chords=10000;maxfit=0
for line in lines('refined.tsv'):
    j,d,at,axis,m,mp,fit,start,last,dup,missing,geom,w=line.split();j,d,at,axis,m,fit,start,last,dup,missing,geom=map(int,(j,d,at,axis,m,fit,start,last,dup,missing,geom))
    from191=archive[d][:at]+str(axis)+archive[d][at:]
    assert shape(from191)<=2
    mf=''.join(mp[int(c)] for c in mothers[m]);assert fit==sum(c in from191[2*j:2*j+2] for j,c in enumerate(mf))
    assert all(c in w[2*j:2*j+2] for j,c in enumerate(mf)) and shape(w)==geom
    a,b,soft=even_stats(w);assert (a,b)==(dup,missing) and 40*a+8*b+soft==last
    min_chords=min(geom,min_chords);maxfit=max(maxfit,fit);counts['rows']+=1
answer['full_warm_anneal']={**counts,'best_total_invalid_pairs':min_chords,'max_aligned_pairs':maxfit}
for line in lines('joined.records'):
    typ,i,cut,last,cost,w=line.split();i,cut,last,cost=map(int,(i,cut,last,cost))
    assert len(w)==192 and shape(w)==cost
    req=mothers[centers[i][2]]
    assert all(c in w[2*j:2*j+2] for j,c in enumerate(req))
control_rows=lines('warm.tsv');control_count=Counter()
for line in lines('join_control.tsv'):
    rid,cut,last,w=line.split();rid,cut,last=map(int,(rid,cut,last))
    warm=control_rows[rid].split();idx,rep,L,H,lo,hi,u,v=map(int,warm[:8]);mp,original=warm[8:]
    mf=''.join(mp[int(c)] for c in mothers[best[idx][2]][u:v])
    assert 2<=last-cut<=4 and len(w)==len(original) and w[:2*cut]==original[:2*cut] and w[2*last:]==original[2*last:]
    assert all(c in w[2*j:2*j+2] for j,c in enumerate(mf));validate(w)
    control_count['recovered']+=1;control_count['different']+=w!=original
answer['join_positive']=dict(control_count)
answer['frontier_join']=lines('join.log');answer['independent_catalogue_upper']=lines('independent_bound.log')
answer['arbitrary_upper']=lines('free_exact.log');answer['independent_arbitrary_upper']=lines('free_bound.log')
(D/'audit.json').write_text(json.dumps(answer,indent=2)+'\n')
(D/'witnesses.json').write_text(json.dumps(examples,indent=2)+'\n')
print(json.dumps(answer))
