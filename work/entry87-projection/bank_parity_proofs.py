"""Small exhaustive edge decisions for auxiliary Hamilton cycles from the bank."""
import argparse
import json
from pathlib import Path
from bank_parity import inputs
from parity_skeleton import structure
from solve import save


def bits(mask):
    while mask:
        bit=mask&-mask
        yield bit.bit_length()-1
        mask^=bit


def initial(anchors,parity):
    vertices,adj,_,tips=structure(anchors)
    n=len(vertices)
    label={v:i for i,v in enumerate(vertices)}
    allowed=[sum(1<<label[w] for w in adj[v]) for v in vertices]+[0]
    for v in (tips if parity else vertices):
        i=label[v];allowed[i]|=1<<n;allowed[n]|=1<<i
    return allowed,[0]*(n+1)


def force(live,chosen):
    n=len(live)
    while True:
        change=False
        for i in range(n):
            if live[i].bit_count()<2:return ["few",i]
            if chosen[i].bit_count()>2:return ["many",i]
            mask=live[i]^chosen[i]
            if not mask:continue
            if live[i].bit_count()==2:
                chosen[i]=live[i]
                for j in bits(mask):chosen[j]|=1<<i
                change=True
            elif chosen[i].bit_count()==2:
                live[i]=chosen[i]
                for j in bits(mask):live[j]&=~(1<<i)
                change=True
        if not change:break
    # A closed forced component cannot ever reach the remaining vertices.
    unseen=(1<<n)-1
    while unseen:
        start=unseen&-unseen;todo=start;part=0;closed=True
        while todo:
            bit=todo&-todo;i=bit.bit_length()-1
            part|=bit
            closed&=chosen[i].bit_count()==2
            todo=(todo|chosen[i])&~part
        unseen&=~part
        if closed and part.bit_count()<n:return ["cycle",list(bits(part))]
    return None


def split(live,chosen):
    scores=[]
    for i,ns in enumerate(live):
        if chosen[i]==ns:continue
        undecided=ns&~chosen[i]
        for j in bits(undecided):
            if i>=j:continue
            score=min(undecided.bit_count(),(live[j]^chosen[j]).bit_count())
            scores.append((score,undecided.bit_count()+(live[j]^chosen[j]).bit_count(),i,j))
    if not scores:raise ValueError("Hamilton cycle survives")
    return min(scores)[2:]


def branch(live,chosen,edge,include):
    i,j=edge
    assert live[i]>>j&1 and not chosen[i]>>j&1
    L=live.copy();C=chosen.copy()
    if include:C[i]|=1<<j;C[j]|=1<<i
    else:L[i]&=~(1<<j);L[j]&=~(1<<i)
    return L,C


def prove(live,chosen):
    terminal=force(live,chosen)
    if terminal:return terminal
    edge=split(live,chosen)
    return ["split",*edge,*[prove(*branch(live,chosen,edge,b)) for b in (False,True)]]


def check(live,chosen,tree):
    terminal=force(live,chosen)
    if terminal:
        assert tree==terminal
        return 1
    assert tree[0]=="split" and len(tree)==5
    return 1+sum(check(*branch(live,chosen,tree[1:3],b),tree[3+b]) for b in (0,1))


if __name__=="__main__":
    parser=argparse.ArgumentParser();parser.add_argument("results",type=Path)
    args=parser.parse_args();rows=json.loads(args.results.read_text())
    cases=dict(inputs());proofs=[];max_nodes=0
    for row in rows:
        p=row["parity"];i=row["index"]
        if "duplicate" in row:continue
        tests=([[]] if row["unchanged"]=="Hamilton path infeasible" else [])
        tests += [edit for edit,reason in row.get("exceptions",[]) if reason=="Hamilton path infeasible"]
        for edit in tests:
            k=len(edit)//2;anchors=set(cases[i][p::2])-set(edit[:k])|set(edit[k:])
            tree=prove(*initial(anchors,p))
            n=check(*initial(anchors,p),tree);max_nodes=max(n,max_nodes)
            proofs.append(dict(index=i,parity=p,edit=edit,nodes=n,tree=tree))
    save(Path(args.results.stem+"-trees.json"),proofs)
    print(len(proofs),sum(r["nodes"] for r in proofs),max_nodes,flush=True)
