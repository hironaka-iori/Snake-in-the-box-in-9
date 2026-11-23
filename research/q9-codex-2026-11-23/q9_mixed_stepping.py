"""Try to reach a private mixed-parent snake first, test its tips, and retain distinct forms."""
import json,sys
from search_q9_anchored_sets import search
from q9_reversal_stepping_stones import sym_key
from search_q9_two_flexible_ends import verify

def extend(p,remaining):
    if remaining==0:return p
    for reverse in (False,True):
        a=p[::-1] if reverse else p
        for d in range(9):
            v=a[-1]^(1<<d)
            if v in a or any((v^u).bit_count()==1 for u in a[:-1]):continue
            w=extend(a+[v],remaining-1)
            if w:return w
    return None

known=set()
for l in open('/tmp/q9_project_records_input9'):
    _,*seq=map(int,l.split())
    # All 190- or 189-edge contiguous subpaths of the known 191 bank are accounted for.
    for n in (189,190,191):
        for i in range(len(seq)-n+1):known.add(sym_key(seq[i:i+n]))
seen=set()
for st,raw,_ in map(json.loads,open('q9_mixed_parents_192.jsonl')):
    if st not in ('UNKNOWN','UNSAT'):continue
    mask=int(raw,16);fixed={x for x in range(512) if mask>>x&1}
    result=[]
    for n in (191,190):
        s,p=search(fixed,fixed,n,3500)
        result.append([n,s])
        if not p:continue
        verify(p,n)
        form=sym_key([(x^y).bit_length()-1 for x,y in zip(p,p[1:])])
        if form in seen:break
        seen.add(form);w=extend(p,192-n)
        if w:verify(w,192)
        print(json.dumps(["SEED",raw,n,form not in known,p,w],separators=(",",":")),flush=True)
        if w:sys.exit()
        break
    print(json.dumps(["CHECK",raw,result],separators=(",",":")),flush=True)
