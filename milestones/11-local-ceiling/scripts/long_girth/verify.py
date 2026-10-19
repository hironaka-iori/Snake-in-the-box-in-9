"""Independent verifier: S subset of Q9 (JSON key 'S' or plain list), checks induced degree == 2
for every vertex, and lists component (cycle) lengths. usage: python verify.py file.json [file2 ...]"""
import sys, json
for f in sys.argv[1:]:
    d = json.load(open(f)); S = d['S'] if isinstance(d, dict) else d
    assert all(0 <= x < 512 for x in S) and len(set(S)) == len(S)
    Ss = set(S)
    adj = {x: [x ^ (1 << k) for k in range(9) if x ^ (1 << k) in Ss] for x in Ss}
    bad = [x for x in Ss if len(adj[x]) != 2]
    seen = set(); lens = []
    for s in Ss:
        if s in seen: continue
        # walk the component; with all degrees 2 it is a cycle
        comp = 0; st = [s]
        while st:
            x = st.pop()
            if x in seen: continue
            seen.add(x); comp += 1; st += adj[x]
        lens.append(comp)
    # cross-check: each component of a 2-regular graph is a cycle with |E| = |V|
    E = sum(len(a) for a in adj.values()) // 2
    print(f"{f}: v={len(S)} edges={E} deg!=2: {len(bad)} cycles={sorted(lens)} min={min(lens)} "
          f"OK2REG={not bad and E == len(S)}")
