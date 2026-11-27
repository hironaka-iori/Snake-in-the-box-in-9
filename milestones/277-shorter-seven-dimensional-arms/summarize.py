"""Reconstruct and compare R277 eight-dimensional donors and validate both traversals."""
from collections import Counter,defaultdict
from hashlib import sha256
import gzip
import json
import sys
from enumerate_groups import HERE,MS,R270,R272,groups,read,points,wordof,unrooted,ordered,paircheck,write

def old_pool():
    refs={}
    def add(path,words):
        refs[str(path.relative_to(MS))]=dict(sha256=sha256(path.read_bytes()).hexdigest(),words=sorted(set(words)))
    file=MS/"267-fixed-arm-extensions/donor-paths.json.gz"
    assert sha256(file.read_bytes()).hexdigest()==read(file.with_name("donors.json"))["sha256"]
    add(file,[w for w,_ in json.loads(gzip.decompress(file.read_bytes()))])
    path=MS/"246-eight-dimensional-parents/donors.json"
    add(path,[unrooted(r["path"]) for r in read(path)["shapes"]])
    path=R270/"q8-primer-arms.json";add(path,list(read(path)))
    path=R270/"uga270.json";add(path,[r["canonical"] for r in read(path)["paths"].values()])
    path=R270/"opposite-constructions.json"
    add(path,[unrooted(p) for r in read(path)["roots"].values() for p in (r["parent"],r["best"]["B"])])
    path=MS/"271-rebuilt-historical-partners/long-joins.json"
    add(path,[unrooted(p) for r in read(path)["witnesses"] for p in (r["parent"],r["partner"])])
    path=R272/"q8-arms.json";add(path,list(read(path)))
    for directory in sorted(MS.glob("27[3-6]-*")):
        for path in sorted(directory.glob("*-paths.json")):
            obj=read(path)
            if isinstance(obj,dict) and isinstance(obj.get("shapes"),dict):
                keys=list(obj["shapes"])
                assert all(isinstance(k,str) and all(v<8 for v in bytes.fromhex(k)) for k in keys)
                add(path,keys)
    r276=MS/"276-partners-of-optimal-arms"
    for file,key in (("input-arms.json","classification"),("site-neighbours-2.json","shapes")):
        path=r276/file
        shapes=read(path)[key]
        assert all(unrooted(r["path"])==w for w,r in shapes.items())
        add(path,list(shapes))
    return refs

def archive_windows():
    sys.path.insert(0,str(MS/"265-joint-arm-regrowth"))
    from exchange import input_paths
    matches=defaultdict(list);totals=Counter()
    for label,p in input_paths():
        word=wordof(p);totals[len(word)]+=1
        for i in range(len(word)-95):
            seg=word[i:i+96]
            if len(set(seg))>8:continue
            for n in (96,97,98):
                seq=word[i:i+n]
                if len(seq)!=n or len(set(seq))>8:break
                k=min(ordered(seq),ordered(seq[::-1])).hex()
                matches[k].append([label,i])
    return matches,totals

def main():
    primary=read(HERE/"mask-groups.json");audit=read(HERE/"contacts-groups.json");gs=groups()
    assert primary.keys()==audit.keys()=={str(i) for i in range(len(gs))}
    refs=old_pool();old=set().union(*(r["words"] for r in refs.values()))
    lengths=(96,97,98)
    intervals={min(ordered(s[i:i+n]),ordered(s[i:i+n][::-1])).hex() for w in old for s in [bytes.fromhex(w)]
               for n in lengths for i in range(len(s)-n+1)}
    archival,archive_sources=archive_windows()
    examples={};multiple=Counter();root_hits=Counter();relaxed=Counter();labelled=Counter()
    for i,group in enumerate(gs):
        first=primary[str(i)];second=audit[str(i)]
        for field in ("relaxed_lengths","paths_sha256","compatible"):assert first[field]==second[field]
        relaxed.update({int(k):v for k,v in first["relaxed_lengths"].items()})
        for r in first["compatible"]:
            key=r["root"];p=points(bytes.fromhex(key));q=list(bytes.fromhex(r["partner"]));s=r["shape"]
            assert key in group["members"] and set(p)&set(q)=={0} and p[0]==q[0]==0
            j=p[::-1]+[128+x for x in q];n=len(j)-1
            pairs=paircheck(j,8)
            assert s==unrooted(j) and n>=96 and wordof(j).count(7)==1
            labelled[n]+=1;multiple[s]+=1;root_hits[key]+=1
            if s not in examples:
                examples[s]=dict(q8_edges=n,joined_q8=j,parent48=p,parent48_key=unrooted(p),rooted_parent=key,
                                 partner=q,all_pairs=pairs,in_previous_pool=s in old,earlier_interval=s in intervals,in_archived_190_191=s in archival)
    ordered_examples={s:examples[s] for s in sorted(examples)}
    new={s:r for s,r in ordered_examples.items() if s not in old}
    out=HERE/"q8-arms.json";write(out,ordered_examples);write(HERE/"q8-new.json",new)
    write(HERE/"archive-occurrences.json",{k:archival[k] for k in sorted(archival.keys()&examples.keys())})
    counts=lambda seq:dict(sorted(Counter(len(w)//2 for w in seq).items()))
    report=dict(source_shapes=570,roots=1140,groups=len(gs),minimum_opposite_edges=47,relaxed_counts=relaxed,
                labelled_counts=labelled,unique_counts=counts(examples),new_to_old_pool=counts(new),
                outside_all_old_intervals=counts(set(examples)-intervals),archive_q9_sources=archive_sources,
                archive_q8_windows=counts(archival),outside_catalogue_and_q9_windows=counts(set(examples)-intervals-archival.keys()),
                productive_roots=len(root_hits),
                productive_shapes=len({unrooted(points(bytes.fromhex(k))) for k in root_hits}),multiplicities=Counter(multiple.values()),
                primary_nodes=sum(v["nodes"] for v in primary.values()),replay_nodes=sum(v["nodes"] for v in audit.values()),
                local_cuts=sum(v["cuts"]["local"] for v in audit.values()),reach_cuts=sum(v["cuts"]["reachable"] for v in audit.values()),
                masks_avoided=Counter(len(g["common"]) for g in gs),
                group_size_counts=Counter(len(g["members"]) for g in gs),old_whole_shapes=len(old),old_windows=counts(intervals),
                catalogue_sha256=sha256(out.read_bytes()).hexdigest(),new_file_sha256=sha256((HERE/"q8-new.json").read_bytes()).hexdigest(),
                old_sources={k:dict(sha256=r["sha256"],counts=counts(r["words"])) for k,r in refs.items()})
    sources=[R272/"q7-single-crossings.json",R272/"q7-single-crossings-replay.json",R272/"short-arm-groups.json",
             R270/"PrimerPartners.cs",HERE/"ContactReplay.cpp",HERE/"capacity.py"]
    report["source_pins"]={f.as_posix().split("/milestones/")[-1]:sha256(f.read_bytes()).hexdigest() for f in sources}
    write(HERE/"summary.json",report)
    print({k:v for k,v in report.items() if k!="old_sources"},flush=True)

if __name__=="__main__":main()
