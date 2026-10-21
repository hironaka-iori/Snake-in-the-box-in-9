"""Measure interval/subwindow redundancy; no Lean proof is claimed."""
import collections
import itertools
import json
import time
from prepare_count_triples_table import PIN, SOURCE, EXPECTED
import runner as r


def canon(directions):
    seen = {}
    return tuple(seen.setdefault(d, len(seen)) for d in directions)


def main():
    data = r.blob(PIN, SOURCE); assert r.hashbytes(data) == EXPECTED
    rows = json.loads(data)['exclusions']
    intervals = sorted({tuple(b) for row in rows for b in row['alpha']})
    index, retained, derived = {}, [], []
    start = time.monotonic()
    order = sorted(enumerate(rows), key=lambda ir: (len(ir[1]['alpha']),
                   -sum(b-a for a,b in ir[1]['alpha']), ir[0]))
    for i, row in order:
        ds = tuple(row['dirs']); bounds = tuple(map(tuple, row['alpha'])); n = len(bounds)
        hit = None
        for k in range(2, n+1):
            if hit: break
            for offset in range(n-k+1):
                if hit: break
                sub = ds[offset:offset+k+1]; values = bounds[offset:offset+k]
                for reverse in [False, True]:
                    shape = canon(sub[::-1] if reverse else sub)
                    values_here = values[::-1] if reverse else values
                    choices = [[b for b in intervals if b[0] <= a and z <= b[1]] for a,z in values_here]
                    for candidate in itertools.product(*choices):
                        witness = index.get((shape, candidate))
                        if witness is not None:
                            hit = dict(index=i, witness=witness, offset=offset, centres=k, reverse=reverse)
                            break
                    if hit: break
        if hit:
            derived.append(hit)
        else:
            retained.append(i); index[(canon(ds), bounds)] = i
    # Independently validate every saved projection witness against original rows.
    for edge in derived:
        whole = rows[edge['index']]; witness = rows[edge['witness']]
        offset, k = edge['offset'], edge['centres']
        ds = whole['dirs'][offset:offset+k+1]
        bs = whole['alpha'][offset:offset+k]
        if edge['reverse']:
            ds, bs = ds[::-1], bs[::-1]
        assert edge['witness'] in retained
        assert canon(ds) == canon(witness['dirs'])
        assert len(bs) == len(witness['alpha'])
        assert all(c <= a and b <= d for (a,b),(c,d) in zip(bs, witness['alpha']))
    summary = dict(total=len(rows), retained=len(retained), potentially_redundant=len(derived),
                   retained_by_centres=dict(collections.Counter(len(rows[i]['alpha']) for i in retained)),
                   redundant_by_centres=dict(collections.Counter(len(rows[e['index']]['alpha']) for e in derived)))
    r.atomic(r.HERE / 'data/count-subwindow-redundancy.json', dict(
        source_commit=PIN, source_path=SOURCE, source_sha256=EXPECTED, script_sha256=r.digest(__file__),
        summary=summary, retained_indices=retained, witnesses=derived, elapsed_seconds=time.monotonic()-start,
        scope='Only interval containment in contiguous subwindows, including reversal and equal-length containment. '
              'Retained does not mean mathematically minimal; no Lean derivation or refutation is asserted.',
        decision='This rule removes only about 4.6 percent; it does not materially shrink the main certificate gap.'))
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
