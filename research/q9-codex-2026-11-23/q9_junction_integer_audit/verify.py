"""Integer-only replay. Start from the literal anchors, independently propagate in batches."""
import json
import os
import sys
from collections import defaultdict, deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))
from verify_q9_high_port_whole import value
from verify_q9_junction_tree import main as check_tree

V = set(range(512))
N = {v: {v ^ (1 << j) for j in range(9)} for v in V}
COLOUR = [{v for v in V if v.bit_count() % 2 == col} for col in range(2)]


def rows(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def close(anchors, excluded, goal, ep):
    required, available = set(anchors), V - set(excluded)
    while True:
        assert required <= available
        deg = {v: len(N[v] & available) for v in available}
        saturated = {v for v in required if len(N[v] & required) == 2}
        assert all(len(N[v] & required) <= 2 for v in required)
        reserved = {v for v in required if deg[v] == 1}
        quota_end = (1,1) if ep==2 else tuple(2 * int(h==ep) for h in range(2))
        remaining = [quota_end[h]-len(reserved&COLOUR[h]) for h in range(2)]
        assert min(remaining)>=0
        components = {}
        for start in sorted(required):
            if start in components:
                continue
            stack = [(start, None)]
            while stack:
                v, prev = stack.pop()
                assert v not in components, "mandatory cycle"
                components[v] = start
                stack.extend((w, v) for w in (N[v] & required) if w != prev)
        must, forbid = set(), set()
        for h, hset in enumerate(COLOUR):
            if goal is None:
                continue
            quota = goal // 2 + int(h == ep)
            assert len(required & hset) <= quota <= len(available & hset)
            if len(required & hset) == quota:
                forbid |= (available - required) & hset
            if len(available & hset) == quota:
                must |= available & hset
        for v in available:
            minimum = 1 if v in reserved or remaining[v.bit_count()%2] > 0 else 2
            if v in required:
                assert deg[v] >= minimum
                if deg[v] == minimum:
                    must |= N[v] & available
                continue
            contacts = N[v] & required
            joins_same = len({components[w] for w in contacts}) < len(contacts)
            if deg[v] < minimum or len(contacts) > 2 or contacts & saturated or joins_same:
                forbid.add(v)
        assert not (must | required) & forbid
        if must <= required and not forbid:
            return required, available
        required |= must
        available -= forbid


def main():
    os.chdir(ROOT)
    tree = check_tree()
    q = deque((set(r['fixed']), set(r['excluded'])) for r in rows(ROOT/'q9_junction_second_omission.jsonl') if r['status']=='UNKNOWN')
    for r in rows(ROOT/'q9_junction_branch.jsonl'):
        f, x = q.popleft()
        if r['status']=='UNKNOWN':
            s = r['split']
            q.extend(((f | {s}, x), (f, x | {s})))
    common = set.intersection(*(f for f, x in q)), set.intersection(*(x for f, x in q))
    original = set(rows(ROOT/'q9_junction_first_omission.jsonl')[0]['fixed'])
    assert common == (original | {144}, {26, 508}) and len(original)==75
    trials = rows(HERE/'trials.jsonl')
    by_idx = {r['index']:r for r in trials}
    positive = by_idx[-1]
    p = positive['witness']
    assert positive['goal']==190 and len(p)==191 and len(set(p))==191 and all(v in V for v in p)
    assert all(((p[i]^p[j]).bit_count()==1) == (j==i+1) for i in range(len(p)) for j in range(i+1,len(p)))
    assert set(positive['pinned']) == set(p)
    leaf_values={}
    for i in [-2, *range(len(q))]:
        f,x = common if i==-2 else q[i]
        r = by_idx[i]
        assert (f,x)==(set(r['pinned']),set(r['excluded']))
        cc = json.loads((HERE/f'leaf_duals/r0_goal192_parent{i}_e0.json').read_text())
        assert cc['parent']==sorted(f) and cc['goal']==192 and cc['end_colour']==0
        fixed, domain = close(f,x,192,0)
        k=value(cc,fixed,domain,192,0)
        assert k==cc['upper']==r['numerator'] and k<193*cc['scale']
        leaf_values[i]=k
    groups=defaultdict(dict)
    # Fully replay the certs for every common two-colour anchor set, including the weakest found.
    for folder in ('relaxed_duals','shared_duals'):
        for path in sorted((HERE/folder).glob('*.json')):
            c=json.loads(path.read_text())
            if c['upper']<193*c['scale'] and not c['excluded']:
                key=tuple(sorted(c['fixed']))
                assert set(key)<=original and len(key)==len(set(key))
                h=c['ep']
                if h not in groups[key] or c['upper']<groups[key][h][0]:
                    groups[key][h]=(c['upper'],path)
    verified=[]
    for k,g in sorted(groups.items(),key=lambda e:(len(e[0]),e[0])):
        if set(g)!={0,1}:
            continue
        record={'fixed':list(k),'count':len(k),'endpoint_cases':[]}
        for h,(n,path) in sorted(g.items()):
            c=json.loads(path.read_text())
            assert c['ep']==h and c['scale']==10000
            f,d=close(k,[],192,h)
            upper=value(c,f,d,192,h)
            assert upper==n<193*c['scale']
            record['endpoint_cases'].append({'ep':h,'numerator':upper,'scale':c['scale'],'certificate':str(path.relative_to(HERE))})
        verified.append(record)
    assert any(len(item['fixed'])==75 for item in verified)
    p191 = rows(ROOT/'q9_parent_junctions.jsonl')[0]['witness']
    assert len(p191)==len(set(p191))==192 and all(v in V for v in p191)
    assert original<=set(p191) and all(((p191[i]^p191[j]).bit_count()==1)==(j==i+1) for i in range(len(p191)) for j in range(i+1,len(p191)))
    unbounded = defaultdict(dict)
    for path in sorted((HERE/'unbounded_duals').glob('*.json')):
        c=json.loads(path.read_text())
        k=tuple(sorted(c['fixed']))
        h=c['signature']
        assert h in (0,1,2) and set(k)<=original
        f,d=close(k,(),None,h)
        assert (len(f),len(d))==(c['forced'],c['allowed'])
        g,e=(193,0) if h==2 else (192,h)
        upper=value(c,f,d,g,e)
        assert upper==c['upper'] and c['scale']==10000
        if upper < (194 if h==2 else 193)*c['scale']:
            x=unbounded[k].get(h)
            if not x or upper<x[0]:unbounded[k][h]=[upper,str(path.relative_to(HERE))]
    three=[{'fixed':list(k),'count':len(k),'signatures':g,'attained_edges':191} for k,g in sorted(unbounded.items(),key=lambda i:len(i[0])) if set(g)=={0,1,2}]
    assert any(t['count']==75 for t in three)
    print(json.dumps(dict(arbitrary_length_exact=three,tree=tree,control_edges=len(p)-1,direct_leaf_integer_checks=len(q),common_parent_bound=leaf_values[-2],leaf_numerator_range=[min(leaf_values[i] for i in range(len(q))),max(leaf_values[i] for i in range(len(q)))],best_found_common_anchor=verified[0],original75=next(v for v in verified if v['count']==75),all_paired_sets=[v['count'] for v in verified]),indent=2))


if __name__=='__main__':
    main()
