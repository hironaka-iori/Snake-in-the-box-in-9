"""Reconcile the independent integer bounds and both upper-layer geometries."""
from collections import Counter
from pathlib import Path
import json
from verify_q9_center_avoidance import forms,verify
from verify_q8_free_layer_dual import verify as verify_single_bound
from grow_q8_exchange_bank import norm

def rows(f):return list(map(json.loads,open(f)))
def path(s):
    p=[0]
    for c in s:p.append(p[-1]^1<<int(c))
    verify(p);return p
def main():
    old={forms(path(w),len(w))[0] for w in Path("q8_joint_even_arms.txt").read_text().split()}
    new=set();summary=[]
    proof=rows("q9_two_tip_integer_bounds.jsonl")
    checked={(w,e):u for w,e,u,t,c in proof}
    assert len(checked)==len(proof)
    for wordfile,singlefile,doublefile in [
        ("q8_exchange_new_rooted_arms.txt","q9_exchange_duals_192.jsonl","q9_exchange_two_tip_192.jsonl"),
        ("q8_exchange_second_rooted_arms.txt","q9_exchange_second_duals_192.jsonl","q9_exchange_second_two_tip_192.jsonl")]:
        words=sorted(Path(wordfile).read_text().split(),key=lambda s:(-len(s),s))
        uniq={}
        for word in words:
            p=path(word);key=forms(p,len(word))[0]
            assert key not in old|new and norm(p[::-1]) in words
            uniq.setdefault(key,word)
        new.update(uniq)
        one=rows(singlefile);assert len(one)==len(words)
        single=Counter();double=Counter()
        for i,(idx,w,st,wit,r) in enumerate(one):
            assert (i,words[i],None)==(idx,w,wit) and st in ("EXHAUSTED","DUAL_EXCLUSION")
            assert r["certificate"]["arm"]==path(w)
            verify_single_bound(r)
            if st=="DUAL_EXCLUSION":assert r["vertices_upper"]<r["target_vertices"]
            single[st]+=1
        ids=set();canon=list(uniq.values())
        for i,e,g,st,upper,w in rows(doublefile):
            if i==-1:
                assert st=="FOUND";verify(w);continue
            assert (i,e) not in ids and 0<=i<len(canon) and e in (0,1)
            ids.add((i,e));word=canon[i]
            assert w is None and g==192 and checked[word,e]==upper and st in ("EXHAUSTED","DUAL_EXCLUSION")
            if st=="DUAL_EXCLUSION":assert upper<10000*(192-len(word))
            double[st]+=1
        assert len(ids)==len(words)==len(uniq)*2
        summary.append(dict(new_shapes=len(uniq),lengths=Counter(map(len,uniq)),single_crossing=single,two_crossings=double))
    assert len(proof)==2*len(new)
    return dict(target_edges=192,original_bank_size=len(old),new_parent_shapes=len(new),batches=summary)
if __name__=="__main__":print(json.dumps(main(),indent=2))
