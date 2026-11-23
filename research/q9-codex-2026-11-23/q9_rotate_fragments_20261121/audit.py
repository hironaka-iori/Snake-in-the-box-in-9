from pathlib import Path
import json,collections,gzip,sys
D=Path(__file__).resolve().parent;R=D.parent
def norm(w):
    m={};return ''.join(str(m.setdefault(c,len(m))) for c in w)
def canon(w):return min(norm(w),norm(w[::-1]))
def word(p):return ''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))
def hits(log):
    out={}
    for l in log.read_text().splitlines():
        l=l.split()
        if l[0]!='W':continue
        length,idx,case,n,k,reorder=map(int,l[1:7]);p=list(map(int,l[7:]))
        assert len(p)==length+1 and all(0<=i<512 for i in p) and len(set(p))==len(p)
        assert all(((v^p[j]).bit_count()==1)==(j+1==i) for i,v in enumerate(p) for j in range(i))
        w=canon(word(p));out[w]=dict(length=length,source_bank_index=idx,trial=case,retained=n,fragments=k,nonmonotone_order=bool(reorder),vertices=p)
    return out
def main():
    control=hits(D/'positive.log');shuffled=hits(D/'shuffled_control.log');rows={};flagged={};example=None;maxrank=(0,0)
    for f in sys.argv[1:]:
        inp="one_bank.txt" if f=="systematic.log" else "bank.txt"
        inputs=[list(map(int,l.split())) for l in (D/inp).read_text().splitlines()]
        for w,r in hits(D/f).items():
            rows[w]=r
            if not r["nonmonotone_order"]:continue
            flagged[w]=r
            original=inputs[r["source_bank_index"]];output=r["vertices"]
            ix={v:i for i,v in enumerate(original) if original.count(v)==1}
            runs=[];start=0
            while start<len(output)-1:
                t=ix.get(output[start],-900);u=ix.get(output[start+1],900);step=u-t
                if abs(step)!=1:start+=1;continue
                end=start+1
                while end+1<len(output) and ix.get(output[end+1],-900)==t+step*(end+1-start):end+=1
                if end+1-start>=5:runs.append([start,end,t,ix[output[end]]])
                start=end
            keys=[min(a[2:]) for a in runs]
            if keys!=sorted(keys) and keys!=sorted(keys,reverse=True):
                rank=len(w),sum(x[1]-x[0]+1 for x in runs)
                if rank>maxrank:maxrank=rank;example=dict(log=f,source_input=inp,**r,matching_runs_output_then_input=runs)

    lengths={len(w) for w in rows}
    known=set();sources=[];digits=set('012345678')
    for f in sorted(R.rglob('*.words')):
        if D in f.parents:continue
        seen=0
        with f.open(errors='replace') as inp:
            for ln in inp:
                s=ln.strip()
                if len(s) in lengths and not set(s)-digits:known.add(canon(s));seen+=1
        if seen:sources.append((str(f.relative_to(R)),seen))
    for line in gzip.open(R/'q9_port_followup_public191.txt.gz','rt'):known.add(canon(word(list(map(int,line.split())))))
    new={w:v for w,v in rows.items() if w not in known}
    for n in (190,191,192):
        (D/f'outside_plain{n}.words').write_text(''.join(w+'\n' for w in sorted(new) if len(w)==n))
    def hist(items):return dict(collections.Counter(map(len,items)))
    reord=flagged
    candidates=new or rows
    best=max(candidates,key=lambda w:(len(w),candidates[w]['nonmonotone_order']))
    bestall=max(rows,key=lambda w:(len(w),rows[w]['nonmonotone_order']))
    report=dict(witnesses=hist(rows),all_checks=sum((len(w)+1)*len(w)//2 for w in rows),control_classes=hist(control),comparison_categories=hist(known),comparison_sources=sources,new_relative_to_comparison=hist(new),reordered=hist(reord),best_witness=rows[bestall],independent_nonmonotone_example=example,shuffled_control=(D/'shuffled_control.log').read_text().splitlines()[-1],strongest_novel_candidate=candidates[best] if new else None,runs={f:(D/f).read_text().splitlines()[-1] for f in sys.argv[1:]},positive=(D/'positive.log').read_text().splitlines()[-1])
    (D/'verified.json').write_text(json.dumps(report,indent=2)+'\n')
    print(hist(rows),hist(known),hist(new),hist(reord),len(sources))
if __name__=='__main__':main()
