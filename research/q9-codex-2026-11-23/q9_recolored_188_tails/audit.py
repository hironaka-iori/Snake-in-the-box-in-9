from pathlib import Path
from collections import Counter
import json
D=Path(__file__).resolve().parent
R=D.parent
def rows(f):return [json.loads(l) for l in (D/(f+'.jsonl')).open()]
def verify(p):
    assert len(set(p))==len(p) and min(p)>=0 and max(p)<512
    neighbors={(min(v,v^(1<<a)),max(v,v^(1<<a))) for v in p for a in range(9) if (v^(1<<a)) in p}
    actual={tuple(sorted(pair)) for pair in zip(p,p[1:])}
    assert actual==neighbors
    for i,x in enumerate(p):
        for j,y in enumerate(p[:i]):assert ((x^y).bit_count()==1)==(i==j+1)
def path(w):
    v=[0]
    for s in w:v.append(v[-1]^(1<<int(s)))
    return v
def word(v):return ''.join(str((a^b).bit_length()-1) for a,b in zip(v,v[1:]))
def groupok(v,z):
    verify(v);l=z.get('l',z.get('left'));h=z.get('r',z.get('right'))
    assert len(v)-1==len(z['w'])+l+h
    grp={x:g for g,ps in enumerate(z['ps']) for x in ps};grp[z['s']]=4
    assert [grp[int(a)] for a in word(v)[l:len(v)-1-h]]==[grp[int(a)] for a in z['w']]
def chords(w):
    p=path(w);n=w.index('8');assert w.count('8')==1
    assert len(p)==len(set(p));verify(p[:n+1]);verify(p[n+1:])
    return len({x&255 for x in p[:n+1]}&{x&255 for x in p[n+1:]})
catalog=(R/'q8_catalogue_96_98.words').read_text().split()
fixed=(D/'registered_arms.txt').read_text().split()
q8=json.loads((D/'q8_bank.json').read_text());sources=Counter()
for lens,items in q8.items():
    n=int(lens);pieces=(n//2,n-1-n//2)
    for item in items:
        def orig(key,length):
            i,a,rev,perm=item[key];w=catalog[i][a:a+length]
            return ''.join(str(perm[int(c)]) for c in (w[::-1] if rev else w))
        w=orig('left',pieces[0])[::-1]+'8'+orig('right',pieces[1])
        assert w==item['word'] and chords(w)==item['common']
        sources['sampled_placements']+=1
for kind in ['aligned','registered']:
    for n in [188,191,192]:
        for line in (D/f'{kind}{n}.txt').open():
            c,job,ai,ao,ar,bi,bo,br,perm,w=line.split();ai,ao,ar,bi,bo,br=map(int,(ai,ao,ar,bi,bo,br));a=(fixed if kind=='registered' else catalog)[ai][ao:ao+n//2];b=catalog[bi][bo:bo+n-1-n//2]
            if ar:a=a[::-1]
            if br:b=b[::-1]
            assert a[::-1]+'8'+''.join(perm[int(k)] for k in b)==w and chords(w)==int(c)
            sources[kind]+=1
small=[];control=[]
for f in ('control','control5'):
    z=rows(f);small.append(z[0]['small'])
    for x in z[1:]:
        groupok(x['path'],x);assert x['status']=='FOUND'
        try:verify(path(x['w']))
        except AssertionError:pass
        else:raise AssertionError('uncorrupted')
        control.append((len(x['w']),x['l'],x['r']))
retry={(z['source'],z['line']):z for z in rows('retry')}
stats={};totals=Counter();rej=0;saved=[]
for f in ['public','knownq8','q8','onechordfull','onechordmixed','selected','every_public']:
    st=Counter()
    for i,z in enumerate(rows(f)):
        a=retry.get((f,i),z)
        if z['status']=='UNKNOWN' and (f,i) in retry:rej+=1
        if a['status']=='FOUND':groupok(a['path'],z);saved.append(a['path'])
        st[z['target'],a['status']]+=1;totals[z['target'],a['status']]+=1
    stats[f]={f'{k}/{v}':n for (k,v),n in sorted(st.items())}
core_status=Counter(z['status'] for z in rows('onechordfull'));core_count=1;covered={(0,2)}
for f in ('allnear0','allnear1'):
    for z in rows(f):
        if 'counts' in z:
            assert sum(z['counts'].values())==945
            core_status.update(z['counts']);core_count+=1;covered.add((z['idx'],z['offset']))
        elif z['status']=='FOUND':groupok(z['path'],z);saved.append(z['path'])
raw=[word(list(map(int,l.split()))) for l in (R/'q8_complete_single_cross_near_192.txt').open()]
def canon(w):
    def norm(w):
        tbl={};return tuple(tbl.setdefault(c,len(tbl)) for c in w)
    return min(norm(w),norm(w[::-1]))
cores={canon(w[i:i+188]) for w in raw for i in range(5)}
assert all(chords(w)==2 for w in raw)
assert len(cores)==21 and len(covered)==21 and {canon(raw[j][off:off+188]) for j,off in covered}==cores
counts=Counter();reused=0;explicit_offsets=set()
for f in ("explicit0","explicit1"):
    for z in rows(f):
        if "new" in z:
            assert sum(z["new"].values())+z["reused"]==945
            counts.update(z["new"]);counts["UNSAT"]+=z["reused"];reused+=z["reused"];explicit_offsets.add(z["offset"])
        elif z["status"]=="FOUND":groupok(z["path"],z);saved.append(z["path"])
assert len(explicit_offsets)==4
public_rows=rows("every_public")
assert all({z["idx"] for z in public_rows if z["target"]==g}==set(range(131)) for g in (192,195,196))
explicit_word=word(json.loads((R/"q9_explicit_q8_96_plus_94.json").read_text())["vertices"])
extra={canon(explicit_word[o:o+188]) for o in explicit_offsets}
assert len(extra)==4 and extra.isdisjoint(cores)
out=dict(explicit_q8_full=dict(cores=len(extra),group_assignments=dict(counts),reused=reused),public_seeds_per_target=131,controls_by_dimension=small,long_controls=len(control),control_dimensions={str(k):n for k,n in Counter(control).items()},checked_Q8_input_rows=dict(sources),batches=stats,retried=rej,experimental_rows_by_target={str(k):n for k,n in totals.items()},one_chord_full=dict(raw_windows=25,cores=core_count,group_assignments=dict(core_status)),generic_encoding_check=dict(Counter(z['other_status'] for z in rows('crosscheck'))),target_witnesses=len(saved))
print(json.dumps(out,indent=2))
