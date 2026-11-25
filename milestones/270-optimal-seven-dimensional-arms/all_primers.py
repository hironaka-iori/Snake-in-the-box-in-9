"""Run the complete six-shape Q7 primer family in sequence and verify the resulting Q8 catalogue."""
from argparse import ArgumentParser
from collections import Counter,defaultdict
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import gzip
import json
import subprocess
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
if not (MS/"267-fixed-arm-extensions").is_dir():
    MS=Path("E:/Snake-in-a-box/milestones")
REPS=(10,1,2,3,8,9)


def read(p):
    return json.loads(p.read_bytes())


def write(p,v):
    p.write_text(json.dumps(v,indent=2)+"\n",encoding="utf-8",newline="\n")


def points(word):
    p=[0]
    for i in word:p.append(p[-1]^(1<<i))
    return p


def paircheck(p,d):
    assert len(set(p))==len(p) and all(0<=v<1<<d for v in p)
    for (i,u),(j,v) in combinations(enumerate(p),2):
        assert ((u^v).bit_count()==1) == (j==i+1)
    return len(p)*(len(p)-1)//2


def wordof(path):
    return bytes((a^b).bit_length()-1 for a,b in zip(path,path[1:]))


def ordered(w):
    axes=list(dict.fromkeys(w))
    return bytes(axes.index(c) for c in w)


def unrooted(p):
    w=wordof(p)
    return min(ordered(w),ordered(w[::-1])).hex()


def verify_catalogues(primer_path,historical_path):
    ps=read(primer_path)
    h=read(historical_path)
    rows={int(k.split('-')[-1]):bytes(map(int,v['word'])) for k,v in ps['paths'].items()}
    assert len(rows)==12 and len(set(rows.values()))==12
    undirected={min(ordered(w),ordered(w[::-1])) for w in rows.values()}
    assert len(undirected)==6 and {min(ordered(rows[k]),ordered(rows[k][::-1])) for k in REPS}==undirected
    for k,w in rows.items():
        p=points(w);paircheck(p,7)
        assert p==ps['paths']['Palani-'+str(k)]['q7_parent'] and len(w)==50
        assert ordered(w[::-1])==rows[ps['reversal_pairs'][str(k)]]
    records=defaultdict(list)
    nested=set()
    for k,r in h['paths'].items():
        p=points(map(int,r['word']));paircheck(p,8);w=wordof(p)
        assert len(w)==97 and r['canonical']==unrooted(p)
        records[unrooted(p)].append(k)
        if any(w.count(a)==1 and w.index(a) in (46,50) for a in set(w)):
            nested.add(unrooted(p))
    assert len(nested)==17 and len(records)==18
    q9={}
    for k,w in h['nine_dimensional'].items():
        p=points(map(int,w))
        pairs=paircheck(p,9)
        assert w.index('8')==97 and w.count('8')==1 and w[:97]==h['paths'][k]['word']
        v=p[97];parent=[x^v for x in p[:98][::-1]];other=[(x^v)^256 for x in p[98:]]
        assert set(parent)&set(other)=={0}
        q9[k]=dict(edges=len(w),transition_word=w,path=p,all_pairs=pairs,q8_parent=h['paths'][k]['canonical'],
                    parent_at_crossing=parent,partner_at_crossing=other,opposite_edges=len(other)-1)
    assert sorted(r['edges'] for r in q9.values())==[182,186]
    return ps,rows,h,records,nested,q9


def signatures(shapes):
    groups=Counter()
    for key in shapes:
        word=bytes.fromhex(key)
        counts=[word.count(d) for d in range(8)]
        distance=(points(word)[-1]).bit_count()
        groups[(min(counts),distance)]+=1
    return [dict(min_coordinate_uses=a,endpoint_distance=d,shapes=n) for (a,d),n in sorted(groups.items())]


def historical_windows(records,n):
    result=defaultdict(set)
    for shape,labels in records.items():
        word=bytes.fromhex(shape)
        for start in range(len(word)-n+1):
            code=unrooted(points(word[start:start+n]))
            result[code].update(labels)
    return result


def extent(shapes):
    # All isometry classes from one free-end addition in Q8, with either
    # endpoint chosen; these may leave the original single-crossing family.
    rows={}
    for shape in sorted(shapes):
        path=points(bytes.fromhex(shape))
        ends={}
        for end,p in enumerate((path,path[::-1])):
            legal={}
            for axis in range(8):
                v=p[-1]^(1<<axis)
                if v in p or any((v^w).bit_count()==1 for w in p[:-1]):continue
                q=p+[v]
                paircheck(q,8)
                legal[axis]=unrooted(q)
            ends[str(end)]=legal
        rows[shape]=ends
    return rows





def summarize(args):
    primers=HERE/"palani-q7.json";history=HERE/"uga270.json"
    ps,rows,h,records,nested,controls=verify_catalogues(primers,history)
    old_file=MS/"267-fixed-arm-extensions/donor-paths.json.gz"
    raw=old_file.read_bytes()
    assert sha256(raw).hexdigest()==read(MS/"267-fixed-arm-extensions/donors.json")['sha256']
    bank={w for w,_ in json.loads(gzip.decompress(raw))}
    assert len(bank)==2760
    links={}
    examples={}
    histogram=Counter()
    categories=defaultdict(Counter)
    by_source=defaultdict(set)
    for k in REPS:
        p0=points(rows[k]);kid=sha256(bytes(p0)).hexdigest()
        folder=HERE/("primer-%s-m45-d%d"%(kid[:10],args.depth))
        base=read(folder/"census.json");audit=read(folder/"replay.json")
        assert base['summary']==audit['summary'] and base['summary']['complete']
        assert base['meta']['parent']==p0 and base['meta']['source_sha256']==sha256(primers.read_bytes()).hexdigest()
        # Recreate the full geometric prefix cover independently. A legal
        # child is an unused adjacent site whose entire prefix has no chord.
        expected={}
        for end,full in enumerate((p0,p0[::-1])):
            parent=[v^full[0] for v in full]
            blocked=set(parent[1:]);prefixes=[[0]]
            for _ in range(args.depth):
                nxt=[]
                for p in prefixes:
                    for u in range(128):
                        if u in blocked or u in p:continue
                        if [v for v in p if (v^u).bit_count()==1]==[p[-1]]:
                            nxt.append(p+[u])
                prefixes=nxt
            for p in prefixes:expected[str(end)+'-'+bytes(p).hex()]=(end,parent,p)
        assert expected.keys()==base['shards'].keys()==audit['shards'].keys()
        count_by_end={0:Counter(),1:Counter()}
        arm_shapes_by_end={0:set(),1:set()}
        for tag,(end,parent,pre) in expected.items():
            r=base['shards'][tag];v=audit['shards'][tag]
            assert r['status']==v['status']=='complete' and r['prefix']==v['prefix']==pre
            rawpaths=gzip.decompress((folder/r['paths']).read_bytes())
            assert sha256(rawpaths).hexdigest()==r['plaintext_sha256']==v['plaintext_sha256']
            counts=Counter();shapes=Counter()
            seqs=rawpaths.decode('ascii').splitlines()
            assert len(seqs)==len(set(seqs))==r['emitted']
            for qhex in seqs:
                q=list(bytes.fromhex(qhex))
                assert q[:len(pre)]==pre and set(q)&set(parent)=={0}
                lifted=parent[::-1]+[v+128 for v in q]
                checks=paircheck(lifted,8)
                shape=unrooted(lifted)
                arm_shapes_by_end[end].add(shape)
                counts[len(q)-1]+=1;shapes[shape]+=1
                if shape not in examples:
                    examples[shape]=dict(q8_edges=len(lifted)-1,palani_row=k,crossing_end=end,
                        partner=q,all_pairs=checks,joined_q8=lifted)
                by_source[shape].add((k,end))
                histogram[len(lifted)-1]+=1
            assert {str(n):c for n,c in counts.items()}==r['partner_edges']
            assert dict(shapes)==r['shape_multiplicities']
            count_by_end[end].update(counts)
        links[k]=dict(folder=folder.name,paired_reverse=ps['reversal_pairs'][str(k)],shards=len(expected),
                      labelled_partner_lengths=count_by_end,
                      longest_partner={e:max(c) if c else None for e,c in count_by_end.items()},
                      primer_upper={e:max(c,default=44) for e,c in count_by_end.items()},
                      q8_shapes_by_end={e:dict(Counter(len(w)//2 for w in words)) for e,words in arm_shapes_by_end.items()})
    all_shapes=set(examples)
    assert nested<=all_shapes and all_shapes & records.keys()==nested
    old96=historical_windows(records,96)
    extension_table=extent(all_shapes)
    extension_shapes={value for ends in extension_table.values() for variants in ends.values() for value in variants.values()}
    for w,r in examples.items():
        r['published_96_windows']=sorted(old96.get(w,[])) if len(w)==192 else []
        r['from_round_267']=w in bank
        r['published_sources']=records.get(w,[])
        r['possible_primers_and_ends']=[list(i) for i in sorted(by_source[w])]
        category=('round_267' if w in bank else 'outside_round_267')+(' and historical' if w in records else ' and outside historical')
        categories[len(w)//2][category]+=1
    summary=dict(coverage="All single-crossing Q8 snakes of at least 96 edges with a whole 50-edge Q7 arm, conditional only on the published complete Q7 primer list.",
                 primer_source=ps['url'],primer_pdf_sha256=ps['pdf_sha256'],primer_data_sha256=sha256(primers.read_bytes()).hexdigest(),
                 historic_source_sha256=sha256(history.read_bytes()).hexdigest(),old_collection_sha256=sha256(old_file.read_bytes()).hexdigest(),
                 primer_rows=links,complete=True,directed_primers=12,undirected_primers=6,partner_threshold=45,
                 shape_counts=Counter(len(w)//2 for w in all_shapes),labelled_counts=histogram,shape_categories=categories,
                 total_shapes=len(all_shapes),in_round_267=sorted(all_shapes&bank),outside_round_267=sorted(all_shapes-bank),
                 historical_96_windows_of_enumerated_shapes=sorted(old96.keys()&all_shapes),
                 enumerated_96_outside_round_267_and_historical_windows=sorted(w for w in all_shapes if len(w)==192 and w not in old96 and w not in bank),
                 single_end_extensions=dict(total_shapes=len(extension_shapes),by_length=Counter(len(w)//2 for w in extension_shapes),
                    outside_nested=sorted(extension_shapes-all_shapes),outside_all_three=sorted(extension_shapes-all_shapes-bank-records.keys())),
                 recovered_historical=sorted(all_shapes & records.keys()),outside_both_supplied_collections=sorted(all_shapes-bank-records.keys()),
                 historic_shapes_outside_nested={w:ks for w,ks in records.items() if w not in all_shapes},
                 geometry_at_97=dict(historical=signatures(records),round_267=signatures(w for w in bank if len(w)==194),
                                     all_optimal_primer_shapes=signatures(w for w in all_shapes if len(w)==194)),
                 historical_source_rows=sum(map(len,records.values())),historical_unique_shapes=len(records))
    write(HERE/"q7-primer-summary.json",summary)
    write(HERE/"q8-primer-arms.json",examples)
    write(HERE/"q8-end-extensions.json",extension_table)
    write(HERE/"historical-q9-controls.json",controls)
    print("Q8 shapes",summary['shape_counts'],"labelled",histogram,"categories",dict(categories),flush=True)


def main():
    parser=ArgumentParser()
    parser.add_argument("operation",choices=["census","audit","summarize"])
    parser.add_argument("--only",nargs="+",type=int,choices=REPS)
    parser.add_argument("--depth",type=int,default=1)
    parser.add_argument("--seconds",type=int,default=90)
    args=parser.parse_args()
    if args.operation=="summarize":
        summarize(args);return
    for k in args.only or REPS:
        command=[sys.executable,"-B",str(HERE/"primer_census.py"),"palani-q7.json","--word-key","Palani-"+str(k),
                 "--minimum","45","--depth",str(args.depth),"--seconds",str(args.seconds)]
        if args.operation=="audit":command.append("--audit")
        print("Palani primer",k,args.operation,flush=True)
        subprocess.run(command,check=True)


if __name__=="__main__":
    main()

