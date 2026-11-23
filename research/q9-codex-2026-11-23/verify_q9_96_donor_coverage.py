"""Independently reconcile general logs and enumerate every geometric port branch for Q8 donors of length 96."""
import argparse
import gzip
import json
import zlib
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from verify_q9_intact98_all_crossings import integer_bound, check

SOURCES = [
    'q9_long_arm_anywhere_atleast192', 'q9_bitterman_free_192',
    'q9_bitterman_trims96_free_192', 'q9_free_new_q8_shapes_192',
    'q9_free_extra_193donors_192', 'q9_long_arm_anywhere_deep1',
    'q9_long_arm_anywhere_deep2', 'q9_free55_mothers_192',
]
TARGETS = {(0, 192), (1, 192), (0, 193)}

def canonical(word):
    def orient(w):
        book = dict(zip(dict.fromkeys(w), '01234567'))
        return ''.join(book[x] for x in w)
    return min(orient(word), orient(word[::-1]))

def vertices(word):
    p = [0]
    for c in word:
        check(c in '01234567', 'foreign coordinate')
        p.append(p[-1] ^ (1 << int(c)))
    check(len(set(p)) == len(p) == 97, 'wrong donor length or repeated vertex')
    check(all((x^y).bit_count() != 1 for i,x in enumerate(p) for y in p[i+2:]), 'donor chord')
    return p

@lru_cache(None)
def port_cases(word):
    p = vertices(word)
    forbidden = set(p)
    # Every interior donor vertex already has its two neighbors.
    for x in p[1:-1]:
        forbidden.update(x^(1<<d) for d in range(8))
    possible = sorted(set(range(256))-forbidden)
    out = {}
    max_low = 0
    for n in range(len(possible)+1):
        for extra in combinations(possible,n):
            lower = set(p)|set(extra)
            nb = {v:{v^(1<<d) for d in range(8)}&lower for v in lower}
            if any(len(s)>2 for s in nb.values()): continue
            todo = set(lower)
            comps = []
            while todo:
                q = [todo.pop()]
                for x in q:
                    more = todo&nb[x]
                    q.extend(more)
                    todo -= more
                comps.append(set(q))
            if any(sum(len(nb[x]) for x in comp)!=2*(len(comp)-1) for comp in comps): continue
            max_low = max(max_low,len(lower)-1)
            mandatory = {x for x in lower if not nb[x]}
            tips = sorted(x for x in lower if len(nb[x])==1)
            # Local degree in Q9 before extension to upper facet is 1 or 2.
            for k in range(len(tips)+1):
                for selected_tips in combinations(tips,k):
                    ports = mandatory|set(selected_tips)
                    if not all(ports&comp for comp in comps): continue
                    low_ends = {x for x in lower if len(nb[x])+int(x in ports)==1}
                    ends = 2-len(low_ends)
                    for e in range(ends+1):
                        high = (e,ends-e)
                        full = tuple(high[h]+sum(x.bit_count()%2==h for x in low_ends) for h in range(2))
                        delta = sum(1-2*(x.bit_count()%2) for x in lower)-(full[0]-full[1])//2
                        out[extra,tuple(sorted(ports)),full] = (lower,ports,high,delta)
    return out,max_low

def key(r):
    return tuple(r['added']),tuple(r['ports']),tuple(r['full'])

def general(catalogue):
    outcomes = defaultdict(lambda:defaultdict(set))
    stats = {}
    for f in SOURCES:
        rows = Counter()
        for line in Path(f+'.jsonl').read_text().splitlines():
            r = json.loads(line)
            if not isinstance(r,list) or len(r)!=6 or not isinstance(r[0],str) or len(r[0])!=192: continue
            b,ep,goal,status,num,wit = r
            raw = bytes.fromhex(b)
            check(len(raw)==96 and max(raw)<=7, 'bad source encoding')
            word = canonical(''.join(map(str,raw)))
            if word not in catalogue: continue
            check((ep,goal) in TARGETS and wit is None, 'endpoint triple or positive')
            if status=='DUAL_EXCLUSION': check(type(num) is int and num<(goal+1)*10000, 'bad integer dual comparison')
            elif status=='EXHAUSTED': check(type(num) is int and num>=(goal+1)*10000, 'bad exhaustive row')
            elif status=='EMPTY_FACTOR': check(num is None,'bad empty factor')
            else: check(status=='UNKNOWN','unknown status')
            outcomes[word][ep,goal].add(status)
            rows[status]+=1
        stats[f]=dict(rows)
    done={w for w in catalogue if all(outcomes[w][p]-{'UNKNOWN'} for p in TARGETS)}
    return outcomes,done,stats

def snapshot(path):
    f=Path(path)
    if not f.is_file():return [],False
    if f.suffix=='.gz':
        obj=zlib.decompressobj(31)
        s=obj.decompress(f.read_bytes())
        complete=obj.eof
    else:s=f.read_bytes();complete=s.endswith(b'\n')
    chunks=s.split(b'\n')
    if complete:check(not chunks[-1], f'truncated row in {f}')
    return [json.loads(x) for x in chunks[:-1]],complete

def audit(args):
    raw=Path('q8_catalogue_96_98.words').read_text().split()
    words=[w for w in raw if len(w)==96]
    cat=set(words)
    check(len(cat)==len(words)==726, 'incorrect catalogue')
    for w in cat:
        check(canonical(w)==w,'noncanonical catalogue')
        vertices(w)
    source=Path('q8_single_cross_complete_arms.txt').read_text().split()
    source += [l.split('\t')[-1] for l in Path('q8_mother_search_20261120/mothers.tsv').read_text().splitlines()[1:]]
    old={canonical(w[i:i+96]) for w in source for i in range(len(w)-95)}
    fresh={canonical(w) for w in Path('q9_fresh_mother_lifts_20261120/q9_55mother20.words').read_text().split()}
    check(len(old)==671 and len(fresh)==55 and not old&fresh and old|fresh==cat,'catalogue provenance mismatch')
    generic,done,stats=general(cat)
    output={'catalogue':len(cat),'general_closed':len(done),'source_counts':stats}
    output['general_dual_label_only']=sum(all('DUAL_EXCLUSION' in generic[w][k] for k in TARGETS) for w in done)
    output['general_search_label_required']=len(done)-output['general_dual_label_only']
    all_closed=set(done)
    port_closed=set(); integer_closed=set(); membership=defaultdict(set)
    for fam in ('hard96','last96'):
        pref='q9_'+fam
        statuses,_=snapshot(pref+'_port_search.jsonl')
        rows,eof=snapshot(pref+'_port_duals.jsonl.gz')
        pairs=[(pref+'_retry.jsonl',pref+'_retry_duals.jsonl.gz')]
        if fam=='last96': pairs.insert(0,(pref+'_early4_retry.jsonl',pref+'_early4_d.jsonl.gz'))
        refinements=defaultdict(list); retry_count=0
        for results,cfile in pairs:
            retries,_=snapshot(results);newer,_=snapshot(cfile)
            strong=dict(newer); status={r[0]:r for r in retries}
            check(len(strong)==len(newer) and len(status)==len(retries),'duplicate retry index within file')
            check(status.keys()<=strong.keys(),'retry without certificate')
            for i,t in strong.items():refinements[i].append((t,status.get(i)))
            retry_count+=len(retries)
        indexed={r[0]:r for r in statuses}
        check(len(indexed)==len(statuses),'duplicate port search result')
        check(all(0<=i<len(rows) for i in indexed),'orphan port search result')
        boxes=defaultdict(set);states=Counter();resolved=set();by_integer=set();rechecks=0;max_low=0
        for i,r in enumerate(rows):
            word=r['word'];check(word in cat,'foreign word')
            table,ll=port_cases(word);max_low=max(max_low,ll)
            k=key(r);check(k in table and k not in boxes[word],'missing/repeated port geometry')
            boxes[word].add(k)
            geometry=table[k]
            def test(t,replay):
                low,ports,high,delta=geometry
                check(t['word']==word and key(t)==k,'mismatched retry')
                if t.get('empty'):return
                check(tuple(t['ends'])==high and t['delta']==delta,'endpoint discrepancy')
                cert=t['cert'];num=t['numerator']
                check(type(num) is int and type(cert['scale']) is int and cert['scale']>0,'non-integer bound')
                if replay:check(integer_bound(cert,low,ports,high,delta)==num, 'integer certificate mismatch')
                bound=len(low)-1+num//cert['scale']
                bound-=int(bound%2!=bool(k[2][0]==1))
                check(bound==t['bound'],'bad rounded edge bound')
            test(r,args.replay)
            if args.replay:rechecks+=1
            target=192+int(k[2]==(1,1))
            def final(z,t):
                _,status,steps,wit=z[:4]
                check(wit is None and isinstance(steps,int) and steps>=0,'unexpected witness or count')
                if status=='DUAL':check(t['bound']<target and steps==0,'false dual classification')
                elif status=='EXHAUSTED':check(t['bound']>=target and steps>0,'bad exhaustion')
                elif status=='UNKNOWN':check(steps>0,'bad unknown')
                else:check(status=='EMPTY' and t['empty'],'bad branch classification')
                if len(z)==5:check(z[4]==t.get('bound'),'mismatched retry bound')
                return status
            s='MISSING'
            if i in indexed:s=final(indexed[i],r)
            if r.get('bound',target)<target:by_integer.add((word,k))
            if i in refinements:
                check(s=='UNKNOWN','non-unknown retry')
                for t,z in refinements[i]:
                    test(t,args.replay)
                    if args.replay:rechecks+=1
                    if t.get('bound',target)<target:by_integer.add((word,k))
                    if z is not None:
                        alternative=final(z,t)
                        if alternative!='UNKNOWN':s=alternative
            states[s]+=1
            if s in {'DUAL','EXHAUSTED','EMPTY'}:resolved.add((word,k))
        closed=set();by_int=set()
        for w,seen in boxes.items():
            expected=set(port_cases(w)[0])
            check(seen<=expected,'foreign case')
            if eof:check(seen==expected,'complete certificate stream lacks port case')
            if all((w,k) in resolved for k in expected):closed.add(w)
            if all((w,k) in by_integer for k in expected):by_int.add(w)
        all_closed|=closed;port_closed|=closed;integer_closed|=by_int
        for w in closed:membership[w].add(fam)
        output[fam]=dict(certificate_stream_complete=eof,donors_seen=len(boxes),expected_cases_for_seen=sum(len(port_cases(w)[0]) for w in boxes),
            serialized_cases=len(rows),search_rows=len(statuses),retry_rows=retry_count,states=dict(states),donors_closed_by_integer_bound_only=len(by_int),closed=len(closed),overlap_general_closed=len(done&closed),scheduled_overlap_general=len(set(boxes)&done),low_only_upper=max_low,integer_replays=rechecks)
    output['closed_union']=len(all_closed)
    output['port_cases_closed_donors']=len(port_closed)
    output['port_integer_only_donors']=len(integer_closed)
    output['open_count']=len(cat-all_closed)
    output['open_words']=sorted(cat-all_closed)
    if args.matrix:
        with args.matrix.open('w') as f:
            print('word\tgeneral_three_closed\tport_family\tport_integer_only\teven_192\todd_192\tmixed_193',file=f)
            for w in sorted(cat):
                print(w,int(w in done),','.join(sorted(membership[w])),int(w in integer_closed),*(','.join(sorted(generic[w][k])) for k in ((0,192),(1,192),(0,193))),sep='\t',file=f)
    return output

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--replay',action='store_true',help='recalculate all stored port integer bounds; general job logs carry status and integer objective only')
    p.add_argument('--matrix',type=Path,help='write a per-donor coverage table')
    print(json.dumps(audit(p.parse_args()),ensure_ascii=False,indent=2))
