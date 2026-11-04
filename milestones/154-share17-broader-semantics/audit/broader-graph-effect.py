"""Read-only interval inventory on saved graph rows; no potential computation."""
from pathlib import Path
import datetime, hashlib, json, time
import numpy as np

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text(encoding='utf-8-sig'))
rels = [
    'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz',
    'milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json',
    'milestones/59-extended-share-window/extended/data/model.json',
    'milestones/149-share-credit-tradeoff/audit/graph-review.json',
    'milestones/153-pair-conditioned-share17/audit/pair-query-and-cycle-review.json',
    'milestones/144-countfree-share18/data/share18-impact/removed-indices.json',
    'milestones/144-countfree-share18/data/share18-impact/results.json',
    'milestones/144-countfree-share18/scripts/evaluate_graph.py',
    'milestones/153-pair-conditioned-share17/broader/verification.json',
]
pins = {rel: sha(R / rel) for rel in rels}
prior = read(R / rels[3])
for rel in [rels[0], rels[1], rels[2], rels[5], rels[6], rels[7]]:
    assert pins[rel] == prior['source_files_sha256'][rel], rel
start = time.monotonic()
meta = read(R / rels[1])
extensions = read(R / rels[2])['extensions']
with np.load(R / rels[0]) as archive:
    direction = archive['direction']
    codes = archive['count_code']
for name, array in [('direction', direction), ('count_code', codes)]:
    assert hashlib.sha256(array.tobytes()).hexdigest() == meta['arrays_sha256'][name]
assert len(direction) == len(codes) == 4947008
digits = np.stack([(codes // 6**j % 6 + 1).astype(np.uint8) for j in range(5, -1, -1)], axis=1)
removed = np.array(read(R / rels[5]), dtype=np.int32)
assert np.all(removed[1:] > removed[:-1])
keep = np.ones(len(direction), dtype=bool)
keep[removed] = False
result144 = read(R / rels[6])
assert int(keep.sum()) == result144['edges']

def canon(word):
    names = {}
    return tuple(names.setdefault(int(x), len(names)) for x in word)

target = (0, 1, 2, 0, 3, 2)
exact_counts = np.array([4, 4, 4, 5, 3], dtype=np.uint8)
broad_lo = np.array([4, 0, 4, 0, 3], dtype=np.uint8)
broad_hi = np.array([4, 4, 4, 5, 3], dtype=np.uint8)
matches = {}
inventory = []
for placement, label in [(0, 'eligible_prefix'), (1, 'suffix')]:
    exact_union = np.zeros(len(direction), dtype=bool)
    broad_union = np.zeros(len(direction), dtype=bool)
    for reverse in [False, True]:
        flags = []
        for word in extensions:
            block = word[placement + 2:placement + 8]
            if reverse:
                block = block[::-1]
            flags.append(canon(block) == target)
        recognized = np.array(flags, dtype=bool)[direction]
        five = digits[:, placement:placement + 5]
        if reverse:
            five = five[:, ::-1]
        exact = recognized & np.all(five == exact_counts, axis=1)
        broad = recognized & np.all((five >= broad_lo) & (np.where(five == 6, 21, five) <= broad_hi), axis=1)
        # A second expression makes exclusion of the clipped bucket explicit.
        direct = recognized & np.all(five < 6, axis=1) & (five[:, 0] == 4) & (five[:, 1] <= 4)
        direct &= (five[:, 2] == 4) & (five[:, 3] <= 5) & (five[:, 4] == 3)
        assert np.array_equal(broad, direct)
        assert np.all(~exact | broad)
        assert not np.any(broad & np.any(five == 6, axis=1))
        added = broad & ~exact
        # Every newly included tuple has a strictly smaller second/fourth sum.
        assert np.all(five[added, 1] + five[added, 3] < 9)
        assert not np.any(added & keep)
        assert np.array_equal(exact & keep, broad & keep)
        matches[(placement, reverse)] = (exact, broad)
        exact_union |= exact
        broad_union |= broad
        inventory.append(dict(placement=label, reverse=reverse,
            source_exact=int(exact.sum()), source_broader=int(broad.sum()),
            source_added=int(added.sum()), retained144_exact=int((exact & keep).sum()),
            retained144_broader=int((broad & keep).sum()), retained144_added=int((added & keep).sum())))
    matches[(placement, 'union')] = (exact_union, broad_union)
    inventory.append(dict(placement=label, reverse='union',
        source_exact=int(exact_union.sum()), source_broader=int(broad_union.sum()),
        source_added=int((broad_union & ~exact_union).sum()),
        retained144_exact=int((exact_union & keep).sum()), retained144_broader=int((broad_union & keep).sum()),
        retained144_added=int((broad_union & ~exact_union & keep).sum())))

cycles = {}
saved = read(R / rels[4])
for name, spec in saved['cycles'].items():
    rows = []
    for row in spec['rows']:
        edge = row['edge']
        assert extensions[int(direction[edge])] == row['directions']
        assert digits[edge].tolist() == row['counts']
        assert keep[edge]
        events = []
        for placement, label in [(0, 'eligible_prefix'), (1, 'suffix')]:
            for reverse in [False, True]:
                exact, broad = matches[(placement, reverse)]
                if broad[edge]:
                    events.append(dict(placement=label, reverse=reverse, exact=bool(exact[edge])))
        rows.append(dict(edge=edge, counts=row['counts'], matches=events))
    totals = {}
    for placement, label in [(0, 'eligible_prefix'), (1, 'suffix')]:
        exact, broad = matches[(placement, 'union')]
        totals[label] = dict(exact=sum(bool(exact[x['edge']]) for x in rows),
                             broader=sum(bool(broad[x['edge']]) for x in rows),
                             matched_edges=[x['edge'] for x in rows if broad[x['edge']]])
    cycles[name] = dict(rows=rows, totals=totals)
assert cycles['eleven']['totals']['suffix']['matched_edges'] == [2222339, 2220859]
assert cycles['eleven']['totals']['suffix']['exact'] == cycles['eleven']['totals']['suffix']['broader'] == 2
assert cycles['fourteen']['totals']['suffix']['broader'] == 0

both_exact = matches[(0, 'union')][0] | matches[(1, 'union')][0]
both_broad = matches[(0, 'union')][1] | matches[(1, 'union')][1]
both = dict(source_exact=int(both_exact.sum()), source_broader=int(both_broad.sum()),
            source_added=int((both_broad & ~both_exact).sum()),
            retained144_exact=int((both_exact & keep).sum()), retained144_broader=int((both_broad & keep).sum()),
            retained144_added=int((both_broad & ~both_exact & keep).sum()))
pins[Path(__file__).relative_to(R).as_posix()] = sha(Path(__file__))
out = dict(status='PASS_SAVED_GRAPH_INTERVAL_INVENTORY_ONLY',
    created_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_edges=len(direction), retained144_edges=int(keep.sum()),
    exact_bounds=[[4,4],[4,4],[4,4],[5,5],[3,3]], broader_bounds=[[4,4],[0,4],[4,4],[0,5],[3,3]],
    inventory=inventory, both_placements_union=both, cycles=cycles,
    clipped_symbol=6, clipped_interval=[6,21], clipping_ambiguity=False,
    reason='Every upper bound is at most5. A clipped6 cannot satisfy any coordinate of the target intervals. On the144 retained graph the second-plus-fourth floor9 forces the broader pair upper bounds4 and5 to be attained.',
    new_potential_computed=False, solver_or_Lean_started=False, new_upper_bound=False,
    scope='Read-only membership enumeration of saved source rows and the saved144 removal set. Current144 hypotheses remain conditional. This does not rebuild removals, prove graph coverage, recompute a potential, or assert an actual-snake upper bound.',
    conditional_cycle_effect='Under the149 profile already imposing universal012032 share16, either exact or broader share17 would improve the same two eleven-cycle suffix rows by one. The inherited total5456 would become5458; the fourteen-cycle is unchanged. No new weight or potential certificate is claimed.',
    next_obligation='After Lean completion, apply share17 to the matched suffix rows and recompute the all-edge potential on the chosen current profile. Broader intervals provide no additional row coverage over the exact context on the144 removal set; they may simplify local hypotheses or affect less-restricted graphs.',
    source_files_sha256=pins, checked_array_sha256={k:meta['arrays_sha256'][k] for k in ['direction','count_code']},
    seconds=time.monotonic()-start)
target_json=H/'audit/broader-graph-effect.json';assert not target_json.exists()
target_json.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
lines=['# Broader interval effect on saved graphs','',
       'This is a read-only graph-row inventory. No Lean compiler, solver, graph rebuild, or potential search was run.','',
       '| Placement | Orientation | Source exact | Source broader | Retained exact | Retained broader |',
       '|---|---|---:|---:|---:|---:|']
for row in inventory:
    orient='both' if row['reverse']=='union' else ('reverse' if row['reverse'] else 'forward')
    lines.append(f"| {row['placement']} | {orient} | {row['source_exact']} | {row['source_broader']} | {row['retained144_exact']} | {row['retained144_broader']} |")
lines += ['',f"The source graph has {len(direction):,} rows; the saved milestone144 removal set retains {int(keep.sum()):,}.",
          f"Across both eligible placements, the broader conditions add {both['source_added']:,} source rows and no retained rows.",'',
          'The reason is exact: the retained graph requires the second-plus-fourth count sum to be at least9. The broader bounds make that sum at most9, so those counts must be4 and5. Every added broader row has a smaller pair sum and is already removed. This conclusion concerns that saved removal set and its hypotheses.','',
          'The eleven-cycle has the same two matching suffix rows,2222339 and2220859. The fourteen-cycle has none. Relative to the149 profile with universal012032 share16, either exact or broader share17 would increase the eleven-cycle total from5456 to5458, assuming the local theorem and its integration. Broadening gives no further increase on either saved cycle.','',
          'Clipping is unambiguous: stored6 denotes the interval[6,21], while every target upper bound is at most5. No target match can contain a clipped value.','',
          'Next, complete the local Lean proof, then recompute the all-edge potential with the stronger suffix contribution on the chosen profile. No new potential or upper bound is established by this inventory.','',
          'The adjacent JSON records every input hash and the checked array hashes.']
target_md=H/'audit/broader-graph-effect.md';assert not target_md.exists()
target_md.write_text('\n'.join(lines)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','source_edges','retained144_edges','inventory','both_placements_union','seconds']}))
