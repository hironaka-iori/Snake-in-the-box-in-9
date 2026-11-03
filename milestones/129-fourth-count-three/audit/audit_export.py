"""Independent, read-only audit of milestone 129's saved proof export.

No producer imports, solver calls, Lean calls, or mutation of audited evidence.
Rebuild the tagged formula, decode packed proof data, and check live slot identities.
"""
from pathlib import Path
from itertools import combinations, zip_longest
from collections import Counter
import argparse
import hashlib
import json
import re
import time
from datetime import datetime, timezone

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
PINS = {}


def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()


def pin(p):
    p = p.resolve()
    try:
        name = p.relative_to(R).as_posix()
    except ValueError:
        name = p.as_posix()
    PINS[name] = sha(p)
    return p


def read(p):
    return json.loads(pin(p).read_text(encoding='utf-8-sig'))


def cnf_bytes(n, clauses):
    return (f'p cnf {n} {len(clauses)}\n' + ''.join(
        ' '.join(map(str, c)) + ' 0\n' for c in clauses)).encode('ascii')


def reconstruct(case):
    """Enumerate Q9 clauses and register meanings directly, without producer code."""
    cls, tags, ctrs = [], [], []
    meaning = {v + 1: ['p', v] for v in range(512)}

    def add(c, *t):
        cls.append(c)
        tags.append(list(t))

    def fresh(m):
        n = len(meaning) + 1
        meaning[n] = m
        return n

    def atmost(ls, k, kind):
        if k >= len(ls):
            return
        assert k >= 1
        ci = len(ctrs)
        ctrs.append(dict(index=ci, literals=ls, upper=k, kind=kind))
        rows = [[fresh(['r', ci, i, j]) for j in range(k)] for i in range(len(ls))]
        add([-ls[0], rows[0][0]], 'first', ci, 0)
        for j in range(1, k):
            add([-rows[0][j]], 'zero', ci, j)
        for i in range(1, len(ls)):
            add([-ls[i], rows[i][0]], 'first', ci, i)
            add([-rows[i-1][0], rows[i][0]], 'mono', ci, i-1, 0)
            for j in range(1, k):
                add([-ls[i], -rows[i-1][j-1], rows[i][j]], 'step', ci, i-1, j-1)
                add([-rows[i-1][j], rows[i][j]], 'mono', ci, i-1, j)
            add([-ls[i], -rows[i-1][k-1]], 'over', ci, i-1)

    w = case['window']
    for v in w:
        add([v+1], 'window')
    ends = []
    for v in range(512):
        ns = [(v ^ (1 << k)) + 1 for k in range(9)]
        for a, b, c in combinations(ns, 3):
            add([-(v+1), -a, -b, -c], 'deg2')
        e = fresh(['e', v])
        ends.append(e)
        add([-(v+1)] + ns, 'degPos')
        add([-e, v+1], 'endSel')
        for j, omitted in enumerate(ns):
            add([-(v+1), e] + [u for u in ns if u != omitted], 'lowEnd', j)
        for a, b in combinations(ns, 2):
            add([-e, -a, -b], 'endLow')
    atmost(ends, 2, ['ends'])
    corners = []
    for i in range(1, len(w)-1):
        used = {(w[i] ^ w[i-1]).bit_length()-1, (w[i] ^ w[i+1]).bit_length()-1}
        cs = [w[i] ^ (1 << a) ^ (1 << b) for a, b in combinations(range(9), 2)
              if a not in used and b not in used]
        assert len(cs) == 21
        corners.append(cs)
        lo, hi = case['bounds'][i-1]
        if hi < 21:
            atmost([-(v+1) for v in cs], hi, ['hi', i-1])
        if lo > 0:
            atmost([v+1 for v in cs], 21-lo, ['lo', i-1])
    for v in range(512):
        for a, b in combinations(range(9), 2):
            if (v >> a) & 1 or (v >> b) & 1:
                continue
            add([-(u+1) for u in [v, v | (1 << a), v | (1 << b), v | (1 << a) | (1 << b)]], 'cut')
        for ds in combinations(range(9), 3):
            if any((v >> k) & 1 for k in ds):
                continue
            cube = [v ^ sum((1 << ds[j]) for j in range(3) if (r >> j) & 1) for r in range(8)]
            for r in range(4):
                add([-(cube[s]+1) for s in range(8) if s not in (r, 7-r)], 'cut')
    atmost(sorted(-(v+1) for cs in corners for v in cs), 22, ['unproved_sum'])
    for cs in case['cycle_cuts']:
        assert len(cs) == len(set(cs)) and cs
        assert all(sum((v ^ (1 << k)) in cs for k in range(9)) >= 2 for v in cs)
        add([-(v+1) for v in cs], 'cut')
    atmost([v+1 for v in corners[1]+corners[3]], 34, ['proved_pair_lower'])
    atmost([v+1 for v in corners[0]], 18, ['lo', 0])
    atmost([v+1 for v in corners[1]], 16, ['lo', 1])
    atmost([-(v+1) for v in corners[3]], 3, ['hi', 3])
    atmost(sorted(-(v+1) for i in (2, 4, 5) for v in corners[i]), 11, ['proved_other_three'])
    return cls, tags, meaning, ctrs, corners


def proof_rows(p):
    with p.open(encoding='ascii') as f:
        for line in f:
            ns = list(map(int, line.split()))
            z = ns.index(0, 1)
            assert ns[-1] == 0 and all(h > 0 for h in ns[z+1:-1])
            yield ns[0], ns[1:z], ns[z+1:-1]


def unpack(n):
    out = []
    while n:
        out.append(n & 8191)
        n >>= 13
    return out


def mask(lits):
    x = 0
    for l in lits:
        assert 0 < abs(l) < 2400
        x |= 1 << (abs(l) + (2400 if l < 0 else 0))
    return x


def decode_lit_word(x):
    assert 1 < x < 4800
    x -= 1
    return x if x < 2400 else -(x-2400)


def main(output):
    started = time.monotonic()
    plan = read(H/'data/proof-plan.json')
    sem = read(H/'data/selected-core-semantics.json')
    core = read(H/'data/core2-search.json')
    previous = read(H/'data/transport-review.json')
    assert previous['status'] == 'PASS_TRANSPORT_AND_COMPLETE_CORE_REFUTATIONS'
    for name, digest in previous['source_files_sha256'].items():
        assert sha(pin(R/name)) == digest, ('earlier evidence changed', name)
    case = read(R/'milestones/125-critical-six-count/data/probes/0120324-total22-positive.json')
    cls, tags, meanings, ctrs, corners = reconstruct(case)
    assert (len(cls), len(meanings), len(ctrs)) == (112225, 10175, 13)
    assert cnf_bytes(10175, cls) == pin(H/'work/expanded.cnf').read_bytes()
    direct = read(R/'milestones/127-direct-cardinality/data/direct-clauses.json')
    assert corners == direct['corner_lists']
    ids = core['core_ids']
    assert ids == sem['core_ids'] and len(ids) == 3500 and ids == sorted(set(ids))
    oldproof = list(proof_rows(pin(H/'work/core2-unsat.mapped.lrat')))
    active = {abs(x) for c in ids for x in cls[c-1]}
    active.update(abs(x) for _, c, _ in oldproof for x in c)
    assert active == set(core['active_variable_ids']) and len(active) == 1695
    order = sorted(active) + sorted(set(range(1, 10176))-active)
    rename = {old: new for new, old in enumerate(order, 1)}
    assert rename == {int(k): v for k, v in sem['old_to_new'].items()}
    assert set(rename) == set(rename.values()) == set(range(1, 10176))
    rl = lambda l: rename[abs(l)] * (1 if l > 0 else -1)
    renamed = [[rl(x) for x in c] for c in cls]
    assert cnf_bytes(10175, renamed) == pin(H/'work/export/triple129.cnf').read_bytes()
    selected = [renamed[i-1] for i in ids]
    raw = [[2*abs(x)+(x < 0) for x in c] for c in selected]
    assert raw == sem['raw'] and [tags[i-1] for i in ids] == sem['tags']
    needed = active | set(range(1, 1025))
    expect_meaning = {str(rename[v]): meanings[v] for v in needed}
    assert expect_meaning == sem['meaning']
    assert len(needed) == sem['semantic_variable_meanings'] == 2415
    assert max(map(int, expect_meaning)) == sem['max_semantic_variable'] == 2415
    assert {tuple(v) for v in expect_meaning.values() if v[0] == 'p'} == {('p', v) for v in range(512)}
    assert {tuple(v) for v in expect_meaning.values() if v[0] == 'e'} == {('e', v) for v in range(512)}
    counter_types = {'first', 'zero', 'mono', 'step', 'over'}
    used = {t[1] for t in sem['tags'] if t[0] in counter_types}
    assert used == {0, 4, 11, 12} == set(sem['used_counter_indices'])
    for i, c in enumerate(ctrs):
        expected = dict(c, literals=[rl(x) for x in c['literals']]) if i in used else dict(index=i, dummy=True)
        assert expected == sem['counters'][i], ('counter mismatch', i)
        if i in used:
            assert all(abs(x) in needed for x in c['literals'])
    assert all(m[1] in used for m in expect_meaning.values() if m[0] == 'r')
    assert sem['window'] == case['window'] == [0, 1, 3, 7, 6, 14, 10, 26]
    assert sem['bounds'] == [[0, 21]]*3 + [[3, 3]] + [[0, 21]]*2
    cnfpath = pin(H/'lean/Recovered129G/LocalWindowCnf/Triple129.lean')
    cnftext = cnfpath.read_text(encoding='utf-8')
    rawbody = cnftext.split('def raw : List (List Nat) := [', 1)[1].split('\n]', 1)[0]
    parsedraw = [[int(x) for x in s.split(',') if x.strip()] for s in re.findall(r'\[([0-9, ]*)\]', rawbody)]
    assert parsedraw == raw
    assert 'window : List Nat := winOf [0,1,2,0,3,2,4]' in cnftext
    assert 'bounds : List (Nat × Nat) := [(0,21),(0,21),(0,21),(3,3),(0,21),(0,21)]' in cnftext
    assert 'cnf : List (List Int) := raw.map (·.map decodeLit)' in cnftext
    proof = list(proof_rows(pin(H/'work/export/triple129.lrat')))
    assert len(proof) == len(oldproof) == 50082
    for a, b in zip(oldproof, proof):
        assert b == (a[0], [rl(x) for x in a[1]], a[2])
    assert max(abs(x) for _, c, _ in proof for x in c) <= 1695
    assert max(abs(x) for c in selected for x in c) <= 1695
    assert sum(len(h) for _, _, h in proof) == 2628221
    assert proof[-1][1] == []

    # Port comparison and dependency-order checks use the saved original bytes.
    files = sorted((H/'generated').rglob('*.lean'))
    assert len(files) == 220
    crlf_sources = 0
    for p in files:
        s = pin(p).read_bytes().decode('utf-8')
        crlf_sources += '\r\n' in s
        s = s.replace('\r\n', '\n')
        expected = re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.Triple129(?:\.[A-Za-z0-9]+)?)$',
                          r'import Recovered129G.\1', s, flags=re.M)
        if p.name == 'Triple129.lean':
            expected += '\n#print axioms Snake9.LocalWindow.Triple129.unsat\n'
        q = pin(H/'lean/Recovered129G'/p.relative_to(H/'generated'))
        assert q.read_bytes() == expected.encode('utf-8'), ('port differs', str(q))
    artifactpaths = {a['path'] for a in plan['artifacts']}
    expectedpaths = {p.relative_to(H).as_posix() for p in (H/'lean/Recovered129G').rglob('*.lean')}
    assert artifactpaths == expectedpaths and len(artifactpaths) == 221
    for a in plan['artifacts']:
        assert sha(pin(H/a['path'])) == a['sha256']
    ordermodules = plan['module_order']
    assert len(ordermodules) == len(set(ordermodules)) == 221
    positions = {m: i for i, m in enumerate(ordermodules)}
    for m, pos in positions.items():
        p = H/'lean'/(m.replace('.', '/')+'.lean')
        assert p.relative_to(H).as_posix() in artifactpaths
        for dep in re.findall(r'^import ([\w.]+)$', p.read_text(encoding='utf-8'), re.M):
            assert dep not in positions or positions[dep] < pos

    # Decode the actual emitted packed data and follow clause identities at each key.
    data = H/'generated/LocalWindowUnsat/Triple129'
    arrays = {}
    for p in sorted(data.glob('Data*.lean')):
        text = p.read_text(encoding='utf-8')
        for name, body in re.findall(r'noncomputable def (inputSlots|proof\d+|cp\d+) : List Nat := \[(.*?)\]', text, re.S):
            assert name not in arrays
            arrays[name] = [int(x, 0) for x in re.findall(r'nat_lit (0x[0-9a-f]+|\d+)', body)]
            assert re.sub(r'nat_lit (0x[0-9a-f]+|\d+)|[\s,]', '', body) == ''
    slots = arrays.pop('inputSlots')
    assert len(slots) == len(set(slots)) == 3500 and max(slots) <= 8191
    assert 'loadRaw (perf 13 0) raw inputSlots' in (data/'Data0.lean').read_text()
    last = {}
    for j, (_, _, hs) in enumerate(proof):
        for cid in hs:
            last[cid] = j
    db = dict(zip(slots, ids))
    masks = {k: mask(c) for k, c in zip(slots, selected)}
    clauses = dict(zip(ids, selected))
    clauses.update({cid: c for cid, c, _ in proof})
    preorder = []
    def walk(lo, hi):
        if hi-lo <= 1:
            return
        mid = (lo+hi)//2
        preorder.append(mid)
        walk(lo, mid)
        walk(mid, hi)
    walk(0, 8192)
    assert len(preorder) == 8191
    j = hints = checkpoints = reused = 0
    allkeys, inputkeys = set(slots), set(slots)
    segmenthints = []
    for segment in range(1, 436):
        cpname = f'cp{segment}'
        if segment > 1 and (segment-1) % 4 == 0:
            cp = arrays.pop(cpname)
            assert len(cp) == 8191
            olddb, oldmasks = db, masks
            db, masks = {}, {}
            for key, packed in zip(preorder, cp):
                if packed:
                    c = [decode_lit_word(x) for x in unpack(packed)]
                    assert key in olddb and c == clauses[olddb[key]], ('checkpoint content', segment, key)
                    db[key] = olddb[key]
                    masks[key] = mask(c)
                elif key in olddb:
                    assert last.get(olddb[key], -1) < j, ('live checkpoint omission', segment, key)
            checkpoints += 1
        words = arrays.pop(f'proof{segment}')
        totalhints = 0
        for packed in words:
            ns = unpack(packed)
            key = ns[0]
            z = ns.index(0, 1)
            c = [decode_lit_word(x) for x in ns[1:z]]
            hs = ns[z+1:]
            cid, wantc, wanths = proof[j]
            assert c == wantc and [db.get(k) for k in hs] == wanths, ('packed alignment', j)
            assert 1 <= key <= 8191 and len(c) < 255 and len(hs) < 4095
            # Independently replay the packed-key RUP propagation using bit masks.
            falsemask = mask(c)
            conflict = False
            for k in hs:
                remain = masks[k] & ~falsemask
                if remain == 0:
                    conflict = True
                    break
                if remain & (remain-1) == 0:
                    bit = remain.bit_length()-1
                    falsemask |= 1 << (bit+2400 if bit < 2400 else bit-2400)
            assert conflict, ('packed RUP failed', j)
            if key in db:
                assert last.get(db[key], -1) <= j, ('premature slot reuse', j, key)
                reused += 1
            db[key], masks[key] = cid, mask(c)
            allkeys.add(key)
            totalhints += len(hs)
            hints += len(hs)
            j += 1
        segmenthints.append(totalhints)
    assert not arrays and j == 50082 and hints == 2628221 and checkpoints == 108
    assert len(allkeys) == 6902
    assert db[key] == proof[-1][0] and masks[key] == 0
    finalkey = key
    assert segmenthints == plan['stats']['seg_hints']
    assert all(v >= 6000 for v in segmenthints[:-1])

    # Inspect the actual checker source and pin the prior object dependency receipt.
    fast = pin(R/'work/final_lean/LratFast.lean').read_text(encoding='utf-8')
    base = pin(R/'work/final_lean/LratCheck.lean').read_text(encoding='utf-8')
    for needle in ['Nat.land x 8191', 'Nat.shiftRight x 13', 'litsL 255', 'hints t 4095', 'Nat.pow 2 2400']:
        assert needle in fast
    assert 'def rawMask' in base and '2400' in base
    receipt = read(Path(plan['checker_receipt']))
    assert receipt['exit_code'] == 0 and not receipt['timeout']
    obj = pin(Path(plan['checker_object']))
    assert sha(obj) == plan['checker_object_sha256'] == receipt['dependencies'][obj.relative_to(R).as_posix()]
    # Verify direct declared source pins, without claiming this is a fresh kernel run.
    for key, p in [
        ('exporter_sha256', H/'scripts/export_proof.py'),
        ('generator_sha256', R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py'),
        ('encoding_sha256', H/'scripts/encoding.py'),
        ('selected_certificate_sha256', H/'data/core2-search.json'),
        ('transport_review_sha256', H/'data/transport-review.json'),
        ('semantic_data_sha256', H/'data/selected-core-semantics.json'),
        ('checker_receipt_sha256', Path(plan['checker_receipt']))]:
        assert plan[key] == sha(pin(p)), key
    assert sem['cnf_source_sha256'] == sha(cnfpath)
    assert sem['selection_sha256'] == plan['selected_certificate_sha256']
    assert sem['script_sha256'] == plan['exporter_sha256']
    pin(Path(__file__))
    for name, digest in PINS.items():
        assert sha(R/name) == digest, ('input changed during audit', name)
    info = dict(
        status='PASS_EXPORTED_BYTES_SEMANTICS_AND_PACKED_PROOF',
        completed_utc=datetime.now(timezone.utc).isoformat(), seconds=time.monotonic()-started,
        scope='Independent Python audit of saved export only. No solver or Lean launched. No actual-snake theorem or global bound claimed.',
        original=dict(variables=10175, clauses=112225, selected_clauses=3500, selected_tags=dict(Counter(t[0] for t in sem['tags']))),
        renaming=dict(bijection_variables=10175, proof_active_variables=1695, max_proof_variable=1695,
                      semantic_meanings=2415, primary_meanings=512, endpoint_meanings=512, inactive_semantic_meanings=720,
                      semantic_indices_above_or_at_offset=sum(int(k)>=2400 for k in sem['meaning']),
                      all_primary_and_endpoint_inputs_retained=True, all_counter_inputs_retained=True),
        retained_counters=[dict(index=i, kind=ctrs[i]['kind'], upper=ctrs[i]['upper'], occurrences=len(ctrs[i]['literals']),
                                distinct_variables=len({abs(x) for x in ctrs[i]['literals']}),
                                selected_clauses=sum(t[0] in counter_types and t[1]==i for t in sem['tags'])) for i in sorted(used)],
        packed_proof=dict(steps=j, hints=hints, segments=435, checkpoints=checkpoints, distinct_slots=len(allkeys),
                          max_key=max(allkeys), reused_keys=reused, full_ordered_hint_id_alignment=True,
                          all_checkpoint_retained_clauses_match=True, no_future_reference_or_premature_reuse=True,
                          complete_packed_RUP_replay=True, final_empty_id=proof[-1][0], final_empty_key=finalkey),
        limits=dict(word_bits=13, key_limit=8191, offset=2400, max_clause=max(len(c) for _,c,_ in proof),
                    max_hints=max(len(h) for _,_,h in proof), literal_fuel=255, hint_fuel=4095),
        sources=dict(generated=220, ported_proof=220, selected_cnf=1, plan_modules=221,
                     all_ports_exact_after_CRLF_to_LF_import_prefix_and_final_print=True,
                     generated_CRLF_sources=crlf_sources, dependency_order_valid=True),
        limitations=['Actual-snake semantic interpretation remains separate.',
                     'Lean replay status is not assessed by this export audit.',
                     'Extra semantic meanings above the literal offset never occur in the selected CNF or proof.',
                     'The retained fourth-count and other-three counters are geometric premises, not derived from old F by the direct prelude.'],
        source_files_sha256=PINS)
    if output:
        with Path(output).open('x', encoding='utf-8', newline='\n') as f:
            json.dump(info, f, indent=2)
            f.write('\n')
    print(json.dumps({k:v for k,v in info.items() if k != 'source_files_sha256'}, indent=2))


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--output')
    main(p.parse_args().output)
