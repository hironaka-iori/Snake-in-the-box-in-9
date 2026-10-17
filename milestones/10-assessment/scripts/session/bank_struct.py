import json, sys, collections, itertools
bank = json.load(open(sys.argv[1]))
def seq(e):
    v = e['vertex_sequence']
    return json.loads(v) if isinstance(v, str) else v
def trans(e):
    t = e['transition_sequence']
    return json.loads(t) if isinstance(t, str) else t
profiles = collections.Counter()
heavyk = collections.Counter()
rows = []
for idx, e in enumerate(bank):
    t = trans(e)
    c = collections.Counter(t)
    counts = sorted((c[k] for k in range(9)), reverse=True)
    profiles[tuple(counts)] += 1
    # light set: coordinates with smallest counts; find best k s.t. top-k carry most
    for k in range(4, 8):
        light = sum(counts[k:])
        rows.append((idx, k, light))
    order = sorted(range(9), key=lambda k: -c[k])
    light5 = sum(counts[5:]); light6 = sum(counts[6:])
    heavyk[(light5, light6)] += 1
print('distinct sorted count profiles:', len(profiles))
for p, n in profiles.most_common(12):
    print(n, p, 'light(top5 heavy)=', sum(p[5:]), 'light(top6)=', sum(p[6:]))
l5 = [sum(sorted((collections.Counter(trans(e))[k] for k in range(9)), reverse=True)[5:]) for e in bank]
l6 = [sum(sorted((collections.Counter(trans(e))[k] for k in range(9)), reverse=True)[6:]) for e in bank]
l4 = [sum(sorted((collections.Counter(trans(e))[k] for k in range(9)), reverse=True)[4:]) for e in bank]
print('transitions in 4 lightest coords (Q5xQ4 split): min/median/max', min(l5), sorted(l5)[len(l5)//2], max(l5))
print('transitions in 3 lightest coords (Q6xQ3 split): min/median/max', min(l6), sorted(l6)[len(l6)//2], max(l6))
print('transitions in 5 lightest coords (Q4xQ5 split): min/median/max', min(l4), sorted(l4)[len(l4)//2], max(l4))
print('min single coordinate count per snake: ', collections.Counter(min(collections.Counter(trans(e))[k] for k in range(9)) for e in bank))
