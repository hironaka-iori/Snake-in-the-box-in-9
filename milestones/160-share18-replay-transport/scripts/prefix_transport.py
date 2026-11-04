"""Check only the accepted144 prefix and emit its materialized checkpoint.

This worker scans the saved proof for allocation metadata. It performs unit
propagation only for the first1055 deductions and never invokes a compiler.
"""
from pathlib import Path
import argparse
import collections
import gzip
import hashlib
import heapq
import json
import os
import re
import time

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
M = R / 'milestones/144-countfree-share18'
PREFIX = 1055
PREFIX_HINTS = 6006
OFF = 8192
WIDTH = 14
SOURCE_CAP = 8*1024**2


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()


def retry_permission(action):
    for attempt in range(40):
        try:
            return action()
        except PermissionError:
            if attempt == 39:
                raise
            time.sleep(.05)


def read(path):
    return retry_permission(lambda:json.loads(Path(path).read_text(encoding='utf-8-sig')))


def save(path, obj):
    payload = (json.dumps(obj, indent=2)+'\n').encode('utf-8')
    temporary = path.with_suffix(path.suffix+'.tmp')
    temporary.write_bytes(payload)
    retry_permission(lambda:temporary.replace(path))


def clauses(path):
    with path.open('r', encoding='ascii') as f:
        for line in f:
            if not line.strip() or line[0] in 'cp':
                continue
            words = list(map(int, line.split()))
            assert words[-1] == 0 and 0 not in words[:-1]
            yield words[:-1]


def proof_rows(path):
    with path.open('r', encoding='ascii') as f:
        for line in f:
            assert len(line) <= 1024*1024, 'Unexpected proof row size'
            words = list(map(int, line.split()))
            assert words and words[-1] == 0
            zero = words.index(0, 1)
            literals, hints = words[1:zero], words[zero+1:-1]
            assert all(h > 0 for h in hints)
            assert len(literals) < 255 and len(hints) <= 4095
            yield words[0], literals, hints


def preorder(height):
    keys = []
    def visit(depth, base):
        if depth:
            key = base+(1 << (depth-1))
            keys.append(key)
            visit(depth-1, base)
            visit(depth-1, key)
    visit(height, 0)
    return keys


def pack(words):
    value = 0
    for word in reversed(words):
        assert 0 <= word < (1 << WIDTH)
        value = (value << WIDTH) | word
    return value


def bit(literal):
    assert 0 < abs(literal) < OFF
    return abs(literal)+(OFF if literal < 0 else 0)


def mask(literals):
    value = 0
    for literal in literals:
        value |= 1 << bit(literal)
    return value


def main():
    assert __debug__
    ap = argparse.ArgumentParser()
    ap.add_argument('--run', type=Path, required=True)
    ap.add_argument('--parent', type=int, required=True)
    args = ap.parse_args()
    run = args.run.resolve(); run.relative_to(H/'data')
    request = read(run/'request.json')
    lock = read(H/'data/prefix-transport.lock')
    assert lock['parent_pid'] == request['parent_pid'] == args.parent
    assert lock['run'] == str(run)
    assert os.environ.get('SNAKE160_PARENT') == str(args.parent)
    preparation = read(H/'data/source-plan.json')
    assert sha(H/'data/source-plan.json') == request['source_plan_sha256']
    for path, digest in {**preparation['source_pins'], **preparation['input_pins']}.items():
        assert sha(R/path) == digest, path
    semantic_progress = R/'milestones/159-share18-proof-continuation/data/semantic-progress.json'
    def verify_terminal159():
        assert not any((semantic_progress.parent/name).exists()
            for name in ['semantic-batch.lock','semantic-final-batch.lock'])
        assert sha(semantic_progress) == request['terminal159_progress_sha256']
        final_path=semantic_progress.with_name('semantic-final-progress.json')
        final=request['terminal159_final_progress']
        if final is None:
            assert not final_path.exists()
        else:
            assert final_path == R/final['path']
            assert sha(final_path) == final['sha256']
    verify_terminal159()

    def progress(phase, **kw):
        save(run/'progress.json', dict(phase=phase, worker_pid=os.getpid(), **kw))

    started = time.monotonic()
    meta = read(M/'data/share144.json')
    ids = meta['core_ids']
    assert ids == list(range(1, 13225))
    assert meta['active_variables'] == 5779
    rename = {int(k):v for k,v in meta['original_to_new'].items()}
    assert len(rename) == 6371 and set(rename.values()) == set(range(1,6372))
    source_ids = read(M/'work/certificate-alternative/core-ids.json')
    assert source_ids == meta['source_original_clause_ids']
    assert len(set(source_ids)) == len(ids)
    compact = list(clauses(M/'certificates/share144.cnf'))
    assert len(compact) == len(ids)
    # This comparison checks the already-applied renaming; the compact LRAT
    # below is used unchanged, with no second variable or input-ID renaming.
    source_ordinals = {cid:i for i,cid in enumerate(source_ids)}
    checked = 0; original_count = 0
    for original_count, clause in enumerate(clauses(M/'work/certificate-alternative/input.cnf'), 1):
        if original_count in source_ordinals:
            mapped = [rename[abs(x)]*(1 if x > 0 else -1) for x in clause]
            assert mapped == compact[source_ordinals[original_count]]
            checked += 1
    assert original_count == 96091 and checked == 13224
    assert all(0 < abs(x) <= 5779 for c in compact for x in c)
    progress('COUNTING_EXACT_COMPACT_PROOF', core_clauses=checked)
    proof = M/'certificates/share144.lrat'
    uses = collections.Counter(); last = {}; seen = set(ids)
    hints_total = 0; literal_total = 0; maximum_hints = 0; previous = 96091
    for i, (cid, literals, hints) in enumerate(proof_rows(proof)):
        assert cid > previous and cid not in seen
        assert all(h in seen for h in hints)
        assert all(0 < abs(x) <= 5779 for x in literals)
        previous = cid; seen.add(cid)
        uses.update(hints)
        for hint in hints:
            last[hint] = i
        hints_total += len(hints); literal_total += len(literals)
        maximum_hints = max(maximum_hints, len(hints))
        if i % 10000 == 0:
            progress('COUNTING_EXACT_COMPACT_PROOF', deductions=i+1, references=hints_total)
    assert (i+1,hints_total,literal_total,maximum_hints) == (145215,14710881,2561006,710)
    assert literals == []
    final_id = cid
    last[final_id] = i+1
    for cid in ids:
        last.setdefault(cid, -1)
    del seen
    order = sorted(ids, key=lambda cid:(-uses[cid], cid))
    slots = {cid:i+1 for i,cid in enumerate(order)}
    initial_slots = [slots[cid] for cid in ids]
    expire = collections.defaultdict(list)
    for cid, at in last.items():
        expire[at].append(cid)
    free = []; next_slot = len(ids)+1
    prefix_steps = []; prefix_ids = []
    allocation_digest = hashlib.sha256()
    # Replay the allocator over the whole proof without replaying deductions.
    # Hints are read before slots whose final use is this row are freed.
    for i, (cid,literals,hints) in enumerate(proof_rows(proof)):
        hint_slots = [slots[h] for h in hints] if i < PREFIX else None
        for old in expire.get(i, []):
            heapq.heappush(free, slots[old])
        target = heapq.heappop(free) if free else next_slot
        if target == next_slot:
            next_slot += 1
        slots[cid] = target
        if cid not in last:
            heapq.heappush(free, target)
        allocation_digest.update(f'{cid}:{target}\n'.encode('ascii'))
        if i < PREFIX:
            prefix_steps.append((cid,target,literals,hint_slots,hints))
            prefix_ids.append(cid)
        if i % 10000 == 0:
            progress('REPRODUCING_EXACT_ALLOCATOR', deductions=i+1, slots=next_slot-1)
    assert i+1 == 145215 and cid == final_id and next_slot-1 == 14114
    assert len(prefix_steps) == PREFIX and sum(len(x[3]) for x in prefix_steps) == PREFIX_HINTS
    assert sum(len(x[3]) for x in prefix_steps[:-1]) < 6000
    keys = preorder(14)
    assert len(keys) == 16383 and (next_slot-1).bit_length() == 14
    key = {slot:keys[i] for i,slot in enumerate(initial_slots)}
    unused = iter(keys[len(ids):])
    for slot in range(1,next_slot):
        if slot not in key:
            key[slot] = next(unused)
    assert len(key) == len(set(key.values())) == 14114
    assert [key[s] for s in initial_slots] == keys[:13224]
    probe = M/'experiments/lean/LiteralProbe144.lean'
    accepted = [int(x,16) for x in re.findall(r'nat_lit 0x([0-9a-fA-F]+)',probe.read_text())]
    assert len(accepted) == PREFIX
    taut = 1 | (1 << OFF)
    db = {k:taut for k in keys}
    entries = {k:0 for k in keys}
    owner = {}
    for cid,slot,clause in zip(ids,initial_slots,compact):
        db[key[slot]] = mask(clause)
        entries[key[slot]] = pack([bit(x)+1 for x in clause])
        owner[slot] = cid
    packed_digest = hashlib.sha256()
    for i,(cid,dest,literals,hint_slots,hints) in enumerate(prefix_steps):
        assert all(owner[s] == h for s,h in zip(hint_slots,hints))
        words = [key[dest]]+[bit(x)+1 for x in literals]+[0]+[key[s] for s in hint_slots]+[0]
        value = pack(words)
        assert value == accepted[i], f'Accepted packed prefix differs at row{i}'
        packed_digest.update((format(value,'x')+'\n').encode('ascii'))
        false_bits = mask(literals); conflict = False
        for slot in hint_slots:
            if conflict:
                continue
            difference = db[key[slot]] & ~false_bits
            if difference == 0:
                conflict = True
            elif difference & (difference-1) == 0:
                b = difference.bit_length()-1
                false_bits |= 1 << (b-OFF if b >= OFF else b+OFF)
            else:
                raise AssertionError(f'Non-unit prefix hint at row{i}')
        assert conflict
        for old in expire.get(i, []):
            assert owner[slots[old]] == old
            owner.pop(slots[old])
        assert dest not in owner
        db[key[dest]] = mask(literals)
        entries[key[dest]] = pack([bit(x)+1 for x in literals])
        owner[dest] = cid
        if cid not in last:
            owner.pop(dest)
    live = {key[slot] for slot,cid in owner.items() if last.get(cid,-1) >= PREFIX}
    checkpoint = [entries[k] if k in live else 0 for k in keys]
    assert len(checkpoint) == 16383
    # Decode independently according to entC, including its special zero case.
    for k,value in zip(keys,checkpoint):
        if value == 0:
            assert k not in live, 'A live empty clause cannot use the tautology marker'
            continue
        decoded = 0; rest = value; count = 0
        while rest:
            word = rest & ((1 << WIDTH)-1)
            assert word > 0
            decoded |= 1 << (word-1)
            rest >>= WIDTH; count += 1
        assert count < 255 and decoded == db[k]
    progress('EMITTING_BOUNDED_CHECKPOINT', verified_prefix_rows=PREFIX, live_clauses=len(live))
    source_options = 'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n'
    data = ('import LratFast144\n'+source_options+'namespace Snake9.Checkpoint160\n'
        'noncomputable def entries : List Nat := [\n'+',\n'.join('nat_lit 0x'+format(x,'x') for x in checkpoint)+']\n'
        'noncomputable def afterPrefix : Snake9.Lrat144.Tree := Snake9.LratFast144.build 14 entries\n'
        'end Snake9.Checkpoint160\n')
    check = ('import CheckpointData160\nimport LiteralProbe144\n'+source_options+
        'namespace Snake9.Checkpoint160\n'
        'theorem checkpoint_ok : Snake9.LratFast144.cpOk\n'
        '    (Snake9.LratFast144.replay Snake9.LiteralData144.start Snake9.LiteralProbe144.proof)\n'
        '    afterPrefix = true := by\n  decide +kernel\n'
        '#print axioms checkpoint_ok\nend Snake9.Checkpoint160\n')
    consequence = ('import CheckpointCheck160\nimport PrefixAssoc146\n'+source_options+
        'namespace Snake9.Checkpoint160\n'
        'theorem afterPrefix_true (τ : Nat → Bool)\n'
        '    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow144.cnf = true) :\n'
        '    Snake9.Lrat144.TreeTrue τ afterPrefix :=\n'
        '  Snake9.LratFast144.cpOk_true τ (Snake9.PrefixAssoc146.checked_prefix_true τ h)\n'
        '    afterPrefix checkpoint_ok\n'
        '#print axioms afterPrefix_true\nend Snake9.Checkpoint160\n')
    sources = {'CheckpointData160':data,'CheckpointCheck160':check,'CheckpointConsequence160':consequence}
    size = sum(len(x.encode('utf-8')) for x in sources.values())
    assert size <= SOURCE_CAP == preparation['limits']['source_bytes']
    output = run/'lean'; output.mkdir()
    artifacts = []
    for module, source in sources.items():
        assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
        path = output/(module+'.lean'); path.write_bytes(source.encode('utf-8'))
        artifacts.append(dict(module=module,path=path.relative_to(run).as_posix(),sha256=sha(path),bytes=path.stat().st_size))
    checkpoint_path = run/'checkpoint-after1055.json.gz'
    checkpoint_path.write_bytes(gzip.compress(json.dumps([format(x,'x') for x in checkpoint],separators=(',',':')).encode('ascii'),mtime=0))
    for path,digest in {**preparation['source_pins'],**preparation['input_pins']}.items():
        assert sha(R/path) == digest, path
    verify_terminal159()
    receipt = dict(status='PASS_EXACT_ACCEPTED_PREFIX_TRANSPORT_CHECKPOINT_SOURCE_ONLY',
        compact_core_clauses=13224, semantic_variables=6371, active_variables=5779,
        allocation_scan_deductions=145215, allocation_scan_references=14710881,
        prefix_deductions=PREFIX,prefix_references=PREFIX_HINTS,packed_rows_equal=PREFIX,
        full_proof_unit_propagation_replayed=False, prefix_unit_propagation_checked=True,
        existing_variable_renaming_preserved=True, second_renaming_applied=False,
        original_input_clause_comparisons=13224,allocator_slots=14114,tree_height=14,word_width=14,
        packed_prefix_hex_lines_sha256=packed_digest.hexdigest(),
        allocation_cid_slot_lines_sha256=allocation_digest.hexdigest(),
        checkpoint_entries=len(checkpoint),live_checkpoint_clauses=len(live),
        checkpoint_file=checkpoint_path.name,checkpoint_sha256=sha(checkpoint_path),
        live_checkpoint_entries_match_prefix_database=True,
        dead_entries_replaced_by_tautologies=True,source_bytes=size,artifacts=artifacts,
        module_order=list(sources),Lean_invoked=False,Lean_checkpoint_checked=False,
        full_share18_replay_complete=False,actual_share18_theorem_complete=False,new_global_bound=False,
        source_plan_sha256=sha(H/'data/source-plan.json'),request_sha256=sha(run/'request.json'),
        seconds=time.monotonic()-started,
        remaining='Check the three generated checkpoint modules in Lean, then separately prepare the remaining full replay.')
    save(run/'prefix-transport.json',receipt)
    progress('FINISHED',status=receipt['status'])
    print(json.dumps({k:receipt[k] for k in ['status','packed_rows_equal','prefix_references','source_bytes','seconds','Lean_checkpoint_checked']}))


if __name__ == '__main__':
    main()
