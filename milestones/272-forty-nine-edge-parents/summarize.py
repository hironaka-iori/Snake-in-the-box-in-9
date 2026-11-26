"""Reconstruct all arms, check every pair, compare source catalogues and calculate free-end extensions."""
from collections import Counter,defaultdict
from hashlib import sha256
from itertools import combinations
import gzip,json
from parents import HERE,R270,read,write,points,wordof,ordered,unrooted,paircheck
from all_primers import extent

def canon(w):
    return min(ordered(w),ordered(w[::-1])).hex()

def summarize():
    ms=HERE.parent
    par=read(HERE/"q7-parents.json"); keys=par["parents"]
    rows=read(HERE/"partners.json");replay=read(HERE/"partner-replay.json")
    needed={w+"/"+str(e) for w in keys for e in (0,1)}
    assert set(rows)==set(replay)==needed
    oldfile=ms/"267-fixed-arm-extensions/donor-paths.json.gz"
    assert sha256(oldfile.read_bytes()).hexdigest()==read(ms/"267-fixed-arm-extensions/donors.json")["sha256"]
    old={w for w,_ in json.loads(gzip.decompress(oldfile.read_bytes()))}
    nested=set(read(R270/"q8-primer-arms.json"))
    history={r["canonical"] for r in read(R270/"uga270.json")["paths"].values()}
    r271=nested|history
    old_windows={canon(bytes.fromhex(k)[i:i+n]) for k in old|r271 for n in (96,97,98) for i in range(len(k)//2-n+1)}
    examples={};multiplicity=Counter();ends={};labels=Counter();sharing=Counter()
    for k in keys:
        for e in (0,1):
            key=k+"/"+str(e);r=rows[key];v=replay[key]
            assert r["complete"] and v["complete"] and v["partners_sha256"]==r["partners_sha256"]
            assert r["partner_lengths"]==v["partner_lengths"]
            p=points(bytes.fromhex(k)[::1 if e==0 else -1]);hits=Counter()
            for qhex in r["partners"]:
                q=list(bytes.fromhex(qhex))
                assert q[0]==p[0]==0 and set(p)&set(q)=={0}
                joined=p[::-1]+[128+v for v in q]
                pairs=paircheck(joined,8)
                w=unrooted(joined);n=len(joined)-1
                assert bytes.fromhex(w).count(7)>=1
                coord=wordof(joined)
                assert [d for d in range(8) if coord.count(d)==1]==[7]
                labels[n]+=1;hits[len(q)-1]+=1;multiplicity[w]+=1
                if w not in examples:
                    examples[w]=dict(q8_edges=n,joined_q8=joined,parent49=p,parent49_key=k,partner=q,crossing_end=e,
                                     all_pairs=pairs,in_round267=w in old,in_round271=w in r271,earlier_interval=w in old_windows)
                else:assert examples[w]["parent49_key"]==k
            assert {str(n):v for n,v in hits.items()}==r["partner_lengths"]
            ends[key]=hits
    assert all(n>=96 for n in labels)
    shapes=set(examples); extensions=extent(shapes)
    bigger={v for ends in extensions.values() for tips in ends.values() for v in tips.values()}
    writable=HERE/"q8-arms.json";write(writable,examples)
    write(HERE/"q8-end-extensions.json",extensions)
    row=dict(parent_families=len(keys),rooted_parents=len(needed),parent_components=list(map(len,par["components"])),
             labelled_counts=labels,shape_counts=Counter(len(bytes.fromhex(k)) for k in shapes),
             inclusive_maximum=max((len(k)//2 for k in shapes),default=95),
             productive_roots=sum(bool(r) for r in ends.values()),productive_parents=len({k.split("/")[0] for k,v in ends.items() if v}),
             new_to_round267=len(shapes-old),new_to_round271=len(shapes-r271),outside_both=len(shapes-old-r271),
             outside_earlier_intervals=len(shapes-old_windows),multiplicities=Counter(multiplicity.values()),
             extensions_by_length=Counter(len(k)//2 for k in bigger),extensions_outside_prior_and_current=sorted(bigger-old-r271-shapes),
             blocked_both_ends=sum(not any(v.values()) for v in extensions.values()),ordered_arm_file_sha256=sha256(writable.read_bytes()).hexdigest(),
             partner_lengths_by_root=ends)
    write(HERE/"summary.json",row)
    print({k:v for k,v in row.items() if k not in ("extensions_outside_prior_and_current","partner_lengths_by_root")},flush=True)
if __name__=="__main__":summarize()
