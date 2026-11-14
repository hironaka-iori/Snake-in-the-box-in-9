"""Independently refute every surviving three-bank-layer case directly with a rooted degree formula."""
import argparse,json
from collections import Counter
from pathlib import Path
from free_last_drat import decide
from free_last_layer import bound
from four_layer_bank import menus
from four_layer_lengths import profiles
from solve import defects,save


def place(menu,previous):
    # Independent implementation. Instead of a shared word trie, try each
    # root-normalized source word separately with first-use isometry pruning.
    forbid=set(previous);root=previous[-1]
    for word in menu:
        mapto={};taken=set()
        def dfs(j,path):
            if j==len(word):
                yield tuple(path);return
            b=word[j];assigned=b in mapto
            for axis in ([mapto[b]] if assigned else range(7)):
                if not assigned and axis in taken:continue
                w=path[-1]^(1<<axis)
                if w in forbid:continue
                if not assigned:taken.add(axis);mapto[b]=axis
                yield from dfs(j+1,path+[w])
                if not assigned:taken.remove(axis);del mapto[b]
        yield from dfs(0,[root])


def generate(domain_index=None, menus_file=None):
    # Cache repeated layer lengths and normalized pair/third placement queries.
    from free_last_layer import trie,placements,vert
    forms={s.encode():v for s,v in json.loads(Path("highdim-seven-39.json").read_text())["forms"].items()}
    if menus_file:
        forms.update({s.encode():v for s,v in json.loads(menus_file.read_text())["forms"].items()})
    bank={n:menus(forms,n) for n in range(40,52)};tries={n:trie(m) for n,m in bank.items()}
    allv=set(range(128));states={};cache={};queries={};counts=Counter()
    for tup in profiles():
        for sizes in (tup,tup[::-1]):
            a,b,c,d=sizes
            pair=(a,b)
            if pair not in cache:
                roots=[]
                for word in bank[a]:
                    A=vert(word)
                    Bs=list(placements(tries[b],A))
                    roots.extend((A,B) for B in Bs)
                cache[pair]=roots
            counts["pairs"]+=len(cache[pair])
            tri=(a,b,c)
            if tri not in states:
                made=[]
                for A,B in cache[pair]:
                    for C in placements(tries[c],B):
                        if C[-1] not in A:made.append((A,B,C))
                states[tri]=made
            for A,B,C in states[tri]:
                root=C[-1];domain=(allv-(set(A)|set(C)))|{root}
                counts["exclusive triples"]+=1
                if bound(domain,root)<d:continue
                key=(tuple(sorted(v^root for v in domain)),d)
                queries.setdefault(key,[]).append((sizes,A,B,C));counts["parity survivors"]+=1
    if domain_index:
        save(domain_index,dict(counts=counts,domains=[dict(domain=key[0],target=key[1],origins=origin) for key,origin in queries.items()]))
    return queries,counts


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=200000);p.add_argument("--proof",action="store_true")
    p.add_argument("--index",type=Path);p.add_argument("--extra-menu",type=Path);a=p.parse_args()
    if a.index and a.index.exists():
        data=json.loads(a.index.read_text());count=data["counts"]
        queries={(tuple(r["domain"]),r["target"]):r["origins"] for r in data["domains"]}
    else:queries,count=generate(a.index,a.extra_menu)
    rows=[];targetfile=Path(f"unrestricted-fourth-{a.first}-{a.stop}-{a.budget}"+("-checked" if a.proof else "")+".json")
    # Solve the rooted path question for every distinct normalized domain
    # and requested final size.
    for i,((domain,k),origins) in enumerate(list(queries.items())[a.first:a.stop],a.first):
        checker=Path("drat-check.exe").resolve() if a.proof else None
        r=decide(domain,k,a.budget,"all-"+str(i),checker)
        if r.get("path"):
            sizes,A,B,C=origins[0];q=[*A,*[x|128 for x in B],*[x|384 for x in C],*[(v^C[-1])|256 for v in r["path"]]]
            assert len(q)==193 and not defects(q);r["vertices"]=q
        rows.append(dict(index=i,target=k,domain=domain,occurrences=len(origins),**r))
        if len(rows)%10==0 or r.get("vertices"):save(targetfile,dict(total=len(queries),counts=count,results=rows))
        if r.get("vertices"):break
    save(targetfile,dict(total=len(queries),counts=count,results=rows));print(len(queries),count,Counter(r["status"] for r in rows),flush=True)
