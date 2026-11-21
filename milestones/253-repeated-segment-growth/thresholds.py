"""Measure exact direct overlaps and closed-component bottlenecks for repeated segment growth."""
from collections import Counter, deque
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parent


def load(path):
    return json.loads(path.read_bytes())


def transitions(path):
    return bytes((u ^ v).bit_length()-1 for u,v in zip(path,path[1:]))


def shape_id(path):
    word = transitions(path)
    def key(w):
        axes=bytes(dict.fromkeys(w))
        return w.translate(bytes.maketrans(axes,bytes(range(len(axes)))))
    return sha256(min(key(word),key(word[::-1]))).hexdigest()


def windows(word,k):
    """Previous occurrence distance, or zero at first use, uniquely identifies an axis partition."""
    if len(word)<k: return
    def directed(w):
        last=[-1]*8
        back=bytearray()
        next_pos=[len(w)]*8
        next_use=[0]*len(w)
        for i in range(len(w)-1,-1,-1):
            a=w[i]; next_use[i]=next_pos[a]; next_pos[a]=i
        for i,a in enumerate(w):
            back.append(i-last[a] if last[a]>=0 else 0); last[a]=i
        result=[]
        for i in range(len(w)-k+1):
            b=back[i:i+k]
            for j in next_pos:
                if j<i+k: b[j-i]=0
            result.append(bytes(b)); next_pos[w[i]]=next_use[i]
        return result
    f=directed(word); r=directed(word[::-1])
    for start,(left,right) in enumerate(zip(f,reversed(r))):
        yield min(left,right),start,left>right


def direct_matrix(words):
    n=len(words)
    matrix=[bytearray(n) for _ in words]
    seen=[(1<<(i+1))-1 for i in range(n)]
    missing=n*(n-1)//2
    for k in range(max(map(len,words)),0,-1):
        masks={}
        for i,w in enumerate(words):
            bit=1<<i
            for key in {s for s,_,_ in windows(w,k)}:
                masks[key]=masks.get(key,0)|bit
        adj=[0]*n
        for mask in masks.values():
            left=mask
            if left & (left-1):
                while left:
                    bit=left&-left
                    adj[bit.bit_length()-1] |= mask
                    left-=bit
        for i in range(n):
            fresh=adj[i]&~seen[i]
            seen[i]|=fresh
            while fresh:
                bit=fresh&-fresh; j=bit.bit_length()-1
                matrix[i][j]=matrix[j][i]=k
                missing-=1; fresh-=bit
        if not missing: break
    if missing: raise ValueError("Unmeasured pair")
    for i,w in enumerate(words): matrix[i][i]=len(w)
    return matrix


def diagonal_best(a,b):
    """Independent longest common segment by maintaining a partial bijection along a diagonal."""
    best=0
    for b in (b,b[::-1]):
        for shift in range(-len(b)+1,len(a)):
            i,j=max(0,shift),max(0,-shift)
            length=min(len(a)-i,len(b)-j)
            if length<=best: continue
            left=0
            last_a=[(-1,-1)]*8; last_b=last_a.copy()
            for pos in range(length):
                x,y=a[pos+i],b[pos+j]
                ax,by=last_a[x],last_b[y]
                if ax[1]!=y: left=max(left,ax[0]+1)
                if by[1]!=x: left=max(left,by[0]+1)
                last_a[x]=(pos,y);last_b[y]=(pos,x)
                best=max(best,pos-left+1)
    return best


def tree(matrix,start,k,edges,minimum):
    parent={start:None}
    todo=deque([start])
    while todo:
        u=todo.popleft()
        if edges[u]<minimum: continue
        for v,d in enumerate(matrix[u]):
            if d>=k and v not in parent:
                parent[v]=u; todo.append(v)
    return parent


def concrete_edge(paths,words,u,v,k):
    left={s:(p,r) for s,p,r in windows(words[u],k)}
    for s,p,r in windows(words[v],k):
        if s not in left: continue
        q,a=left[s]
        source=paths[u][q:q+k+1]; target=paths[v][p:p+k+1]
        rev=a!=r
        if rev: target=target[::-1]
        mapping=dict(zip(transitions(source),transitions(target)))
        unused=sorted(set(range(8))-mapping.keys()); available=sorted(set(range(8))-set(mapping.values()))
        if len(unused)!=len(available): raise ValueError("Segment map is not injective")
        mapping.update(zip(unused,available))
        axes=[mapping[i] for i in range(8)]
        def perm(x): return sum(1<<axes[i] for i in range(8) if x&(1<<i))
        delta=perm(source[0])^target[0]
        if [perm(x)^delta for x in source]!=target: raise ValueError("Segment isometry mismatch")
        return dict(source=u,target=v,edges=k,source_start=q,target_start=p,reverse_target=rev,axes=axes,xor=delta)
    raise ValueError("Missing segment witness")


def main():
    file=HERE/"closure.json"
    donor_file=BASE/"248-rooted-arm-capacity"/"parents.json"
    corner_file=BASE/"249-long-parent-joins"/"geometry.json"
    closure=load(file); floor=closure["core"]
    ids=sorted(closure["paths"]); paths=[closure["paths"][i] for i in ids]
    index={v:i for i,v in enumerate(ids)}
    words=list(map(transitions,paths)); edges=list(map(len,words))
    if not closure["closed"] or closure["minimum_intermediate"]!=96 or set(closure["expanded"])!=set(ids):
        raise ValueError("This analysis requires the complete 96- through 98-edge closure")
    for i,p in enumerate(paths):
        if shape_id(p)!=ids[i] or not 96<=edges[i]<=98:
            raise ValueError("Invalid path identity")
    named={str(r["donor_index"]):index[shape_id(r["path"])] for r in load(donor_file)["rows"]}
    named.update({r["id"]:index[shape_id(r["path"])] for r in load(corner_file)["corner_closure"]["new_shapes"]})
    if set(named.values())!={index[i] for i in closure["seeds"]}: raise ValueError("Reference names differ")
    matrix=direct_matrix(words)
    start=named["20"]
    checked=set()
    for i in named.values():
        targets=range(len(ids)) if i==start else named.values()
        for j in targets:
            pair=tuple(sorted((i,j)))
            if i!=j and pair not in checked:
                if diagonal_best(words[i],words[j])!=matrix[i][j]: raise ValueError("Longest match differs")
                checked.add(pair)
    largest=max(edges)
    forest=[]; groups=list(range(len(ids)))
    def find(i):
        while groups[i]!=i:
            groups[i]=groups[groups[i]];i=groups[i]
        return i
    connect={}
    for i,row in enumerate(matrix):
        for j in range(i+1,len(ids)):
            if row[j]>=floor: connect.setdefault(row[j],[]).append((i,j))
    history={}
    for k in range(largest,floor-1,-1):
        for u,v in connect.get(k,[]):
            a,b=find(u),find(v)
            if a!=b:
                groups[b]=a; forest.append(concrete_edge(paths,words,u,v,k))
        components=Counter(find(i) for i in range(len(ids)))
        labelled={}
        for donor,i in named.items(): labelled.setdefault(find(i),[]).append(donor)
        history[k]=dict(component_sizes=sorted(components.values(),reverse=True),
                        references=[dict(size=components[g],names=names) for g,names in labelled.items()])
    reach={}
    for minimum in (96,97,98):
        results={};sizes={}
        for k in range(largest,floor-1,-1):
            parent=tree(matrix,start,k,edges,minimum)
            sizes[k]=len(parent)
            for i in parent.keys()-results.keys():
                route=[i]
                while route[-1]!=start: route.append(parent[route[-1]])
                route.reverse()
                results[i]=dict(threshold=k,direct=matrix[start][i],route=route)
        reach[minimum]=dict(count_by_threshold=sizes,above_floor=results,
                            outside=[i for i in range(len(ids)) if i not in results])
    counts=Counter(matrix[i][j] for i in range(len(ids)) for j in range(i+1,len(ids)))
    out=dict(closure_sha256=sha256(file.read_bytes()).hexdigest(),source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
             identities=ids,reference_indices=named,closed_threshold=floor,
             direct_upper_triangle=[list(row[i+1:]) for i,row in enumerate(matrix)],pair_counts=counts,
             independent_diagonal_comparisons=len(checked),components=history,maximum_spanning_forest=forest,
             donor20=reach)
    (HERE/"thresholds.json").write_text(json.dumps(out,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    for minimum,rec in reach.items():
        print("Donor 20, minimum intermediate",minimum,":",rec["count_by_threshold"][floor],"reachable;",
              Counter(v["threshold"] for v in rec["above_floor"].values()),flush=True)
    print("Full 68-edge component sizes",history[floor]["component_sizes"],flush=True)
    for tag in ("15","20","30","49","59","69","73"):
        i=named[tag]
        print(tag,"direct",matrix[start][i],"bottleneck",reach[96]["above_floor"].get(i,{}).get("threshold"))


if __name__=="__main__":
    main()
