"""Exact rooted Hamilton witnesses represented as a matching with private endpoints."""
from itertools import product
from pathlib import Path
from paired_seeds import extract
from joint_parity import orders
from solve import save


def compressed(lists):
    # Examine directly the finitely many endpoint/edge obligations and all
    # choices when a given obligation has more than one candidate address.
    # Failure has a Hall certificate: from unmatched left obligations follow
    # alternating edges, then count reachable obligations and addresses.
    owner={};choice={}
    for start in range(len(lists)):
        left={start};right=set();pre={};q=[start];found=None
        while q and found is None:
            i=q.pop()
            for w in lists[i]:
                if w in right:continue
                right.add(w);pre[w]=i
                if w not in owner:
                    found=w;break
                nxt=owner[w]
                if nxt not in left:left.add(nxt);q.append(nxt)
        if found is None:
            assert set.union(*[set(lists[i]) for i in left])==right and len(right)<len(left)
            # Greedily shrink to a minimal explicit Hall obstruction.
            for i in sorted(left):
                other=left-{i}
                if other and len(set.union(*(set(lists[j]) for j in other)))<len(other):
                    left=other
            right=set.union(*(set(lists[j]) for j in left))
            return dict(obligations=sorted(left),addresses=sorted(right))
        w=found
        while w is not None:
            i=pre[w];next_w=choice.get(i);choice[i]=w;owner[w]=i;w=next_w
    return None


if __name__=="__main__":
    rows=[]
    for i,row in enumerate(extract()):
        A=tuple(sorted(row["parent"][::2]));B=tuple(sorted(row["known_partner"][::2]))
        for cap in (0,1):
            left=orders(A,cap==0);right=orders(B,cap==1)
            reasons=[]
            for (la,choices_a),(lb,choices_b) in product(left,right):
                objection=compressed(choices_a+choices_b)
                assert objection
                def describe(j):
                    s=int(j>=len(choices_a));order=lb if s else la
                    j-=len(choices_a) if s else 0
                    return [s,*(order[j:j+2])]
                reasons.append(dict(needs=[describe(j) for j in objection["obligations"]],
                                    addresses=objection["addresses"]))
            rows.append(dict(index=i,odd_end_on=cap,orders=[len(left),len(right)],hall=reasons))
    save(Path("joint-hall.json"),rows)
    print(len(rows),sum(len(r["hall"]) for r in rows),
          sorted(set((len(h["needs"]),len(h["addresses"])) for r in rows for h in r["hall"])))
