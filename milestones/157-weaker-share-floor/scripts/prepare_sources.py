"""Prepare157 source only. Never imports a graph worker or starts a compiler."""
from pathlib import Path
import ast
import hashlib
import json

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
OLD = R / 'milestones/156-potential-range-and-paper'
EXPECTED_PREPARATION = '7319be1786142709414d078183b43b961f4137809351d4c4eee2cd1b053226cb'


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def write(path, content):
    payload = content if isinstance(content, bytes) else content.encode('utf-8')
    if path.exists():
        assert path.read_bytes() == payload, 'Existing prepared file differs: '+str(path)
    else:
        path.write_bytes(payload)


def replace_once(source, old, new):
    assert source.count(old) == 1, old[:100]
    return source.replace(old, new, 1)


WORKER_TAIL = r'''
    # All archived156 assertions above concern the original floor18 profile.
    accepted = read(R / plan['accepted156_result'])
    assert accepted['status'] == 'PASS_MINIMUM_RANGE_AT_MEAN496'
    assert build == accepted['graph'] == read(R / plan['accepted156_graph'])
    save(run / 'original156-reconstruction.json', build)
    n = meta['states']
    archive = R / plan['accepted156_potential']
    assert sha(archive) == accepted['potential_archive_sha256']
    raw = gzip.decompress(archive.read_bytes())
    assert hashlib.sha256(raw).hexdigest() == accepted['potential_sha256']
    baseline = np.frombuffer(raw, dtype='<i8')
    assert len(baseline) == n and int(baseline.min()) == 0 and int(baseline.max()) == 602

    def scan(potential):
        minimum, violations, first = None, 0, []
        for lo in range(0, len(weights), BLOCK):
            hi = min(lo+BLOCK, len(weights))
            slack = weights[lo:hi]+potential[u[lo:hi]]-potential[v[lo:hi]]-496
            value = int(slack.min())
            minimum = value if minimum is None else min(minimum, value)
            bad = np.flatnonzero(slack < 0)
            violations += len(bad)
            for j in bad[:max(0, 20-len(first))]:
                first.append(dict(source_edge=int(ids[lo+j]), slack=int(slack[j])))
        assert minimum is not None
        return dict(minimum_slack=minimum, violation_count=violations,
                    first_violations=first, inequalities=len(weights))

    original_scan = scan(baseline)
    assert original_scan['violation_count'] == 0 and original_scan['minimum_slack'] == 0
    nine = accepted['deficit_walk']
    assert len(nine) == 9 and sum(row['weight'] for row in nine) == 3862
    for row in nine:
        index = row['source_edge']
        assert mask[index]
        assert int(arrays['U'][index]) == row['u'] and int(arrays['V'][index]) == row['v']
        assert int(source17[index]+shared[index]) == row['weight']
        assert bool(matched[index]) == row['share17_match'] is False
    assert all(a['v'] == b['u'] for a, b in zip(nine, nine[1:]))

    # Recompute max(source, count+floor); subtracting one from every012034 row
    # would be incorrect when the inherited source term already dominates.
    target_shape = np.asarray([s == '012034' for s in shapes], dtype=bool)[direction]
    weaker_conditional = conditional.copy()
    weaker_conditional[target_shape] = 17
    weaker_floor = np.maximum(weaker_conditional, np.where(matched, 17, 0))
    weaker_source = np.maximum(source_weight, 120*last+weaker_floor)
    decrease = source17-weaker_source
    assert np.all((decrease >= 0) & (decrease <= 1))
    assert not np.any((decrease != 0) & ~target_shape)
    assert not np.any((decrease != 0) & matched)
    assert all(int(weaker_source[row['edge']]+shared[row['edge']]) == row['conditional_weight']
               for row in fourteen)
    assert sum(int(weaker_source[row['edge']]+shared[row['edge']]) for row in fourteen) == 6944
    nine_changed = []
    for row in nine:
        index = row['source_edge']
        nine_changed.append(dict(source_edge=index, u=row['u'], v=row['v'],
            directions=ds[int(direction[index])], counts=digits[index].tolist(),
            original_weight=row['weight'], weight=int(weaker_source[index]+shared[index]),
            source_weight=int(source_weight[index]), shared_bonus=int(shared[index]),
            share17_match=bool(matched[index])))
    assert [row['weight'] for row in nine_changed] == [252,377,496,496,616,496,496,376,256]
    assert sum(row['weight'] for row in nine_changed) == 3861
    original_graph = build
    weights = (weaker_source+shared)[mask]
    build = dict(states=n, source_edges=len(mask), retained_edges=len(ids),
        original156_graph=original_graph, original156_reproduced=True,
        original156_potential_scan=original_scan,
        weight_sha256=array_sha(weights), source_weight_sha256=array_sha(weaker_source),
        retained_row_ids_sha256=array_sha(ids),
        source_suffix_matches=int(matched.sum()), retained_suffix_matches=int(retained_matches.sum()),
        changed_source_rows=int(np.count_nonzero(decrease)),
        changed_retained_rows=int(np.count_nonzero(decrease[mask])),
        unchanged_target_source_rows=int(np.count_nonzero(target_shape & (decrease == 0))),
        unchanged_target_retained_rows=int(np.count_nonzero(target_shape & (decrease == 0) & mask)),
        maximum_weight_decrease=int(decrease.max()),
        fourteen_cycle_total=6944, fourteen_cycle_unchanged=True,
        nine_walk_total=3861, nine_walk=nine_changed, range_lower_bound_at496=603,
        floors=plan['floors'], pending_floors=plan['pending_floors'])
    save(run / 'graph-reconstruction.json', build)
    del data, arrays, meta, direction, mask, shared, digits, source_weight, source16, source17
    del matched, last, conditional, new_floor, original_floor, old144
    del target_shape, weaker_conditional, weaker_floor, weaker_source, decrease
    gc.collect()
    baseline_scan = scan(baseline)
    # Record failure as evidence; range602 is never used as a search shortcut.
    assert baseline_scan['violation_count'] > 0
    assert baseline_scan['minimum_slack'] == -1
    save(run / 'baseline-certificate.json', dict(status='FAIL_OLD_POTENTIAL_UNDER_WEAKER_FLOOR',
        mean=496, range=602, **baseline_scan, source_archive=str(archive),
        source_archive_sha256=sha(archive), raw_potential_sha256=accepted['potential_sha256'],
        weight_sha256=build['weight_sha256'], original156_scan=original_scan))
    journal = run / 'journal'; journal.mkdir()
    layers = []
    journal_bytes = 0
    maximum_journal = 2*1024**3
    assert n < 2**32 and len(weights) < 2**32
    assert 1503*(496+max(abs(int(weights.min())), abs(int(weights.max())))) < 2**62
    started = time.monotonic()
    deadline = started+600
    dist = np.zeros(n, dtype=np.int64)
    status = 'UNRESOLVED_ITERATION_LIMIT'
    selected = None
    selected_range = None
    endpoint = None
    deficit = 0
    for iteration in range(1, 1501):
        if time.monotonic() >= deadline:
            status = 'UNRESOLVED_TIME_LIMIT'; break
        save(progress, dict(phase='DISCOVERY', worker_pid=os.getpid(), iteration=iteration,
            discovery_started=started, journal_bytes=journal_bytes, maximum_deficit=-int(dist.min())))
        nxt = dist.copy()
        for lo in range(0, len(weights), BLOCK):
            hi = min(lo+BLOCK, len(weights))
            np.minimum.at(nxt, v[lo:hi], dist[u[lo:hi]]+weights[lo:hi]-496)
        if np.array_equal(nxt, dist):
            assert int(dist.max()) == 0
            selected_range = -int(dist.min())
            assert 603 <= selected_range <= 631
            selected = dist+selected_range
            endpoint = int(np.argmin(dist))
            status = 'PASS_MINIMUM_RANGE_AT_MEAN496'; break
        changed = np.flatnonzero(nxt < dist)
        needed = len(changed)*8
        if journal_bytes+needed > maximum_journal or shutil.disk_usage(run).free < needed+512*1024**2:
            status = 'UNRESOLVED_JOURNAL_LIMIT'; break
        predecessor = np.full(n, -1, dtype=np.int64)
        for lo in range(0, len(weights), BLOCK):
            hi = min(lo+BLOCK, len(weights))
            candidate = dist[u[lo:hi]]+weights[lo:hi]-496
            eligible = np.flatnonzero((candidate == nxt[v[lo:hi]]) & (nxt[v[lo:hi]] < dist[v[lo:hi]]))
            np.maximum.at(predecessor, v[lo:hi][eligible], eligible+lo)
        assert np.all(predecessor[changed] >= 0)
        pairs = np.column_stack([changed, predecessor[changed]]).astype('<u4')
        path = journal / ('layer-'+str(iteration).zfill(4)+'.u32')
        pairs.tofile(path)
        assert path.stat().st_size == needed
        layers.append(dict(path=path.relative_to(run).as_posix(), rows=len(changed), sha256=sha(path)))
        journal_bytes += needed
        del predecessor, pairs, changed
        dist = nxt
        deficit = -int(dist.min())
        if deficit >= 632:
            endpoint = int(np.argmin(dist))
            status = 'PASS_FIXED_MEAN_TARGET_OBSTRUCTION'; break
    discovery_seconds = time.monotonic()-started
    # For an unfinished run, retain a checked walk supporting the observed
    # lower bound without claiming that an upper certificate exists.
    if endpoint is None and layers:
        endpoint = int(np.argmin(dist))
    save(progress, dict(phase='FINALIZING', worker_pid=os.getpid(),
        discovery_started=started, discovery_seconds=discovery_seconds, status=status))
    witness = []
    witness_deficit = None
    if endpoint is not None:
        vertex = endpoint
        for layer in reversed(layers):
            path = run / layer['path']
            assert sha(path) == layer['sha256']
            pairs = np.memmap(path, dtype='<u4', mode='r', shape=(layer['rows'], 2))
            index = int(np.searchsorted(pairs[:, 0], vertex))
            if index < len(pairs) and int(pairs[index, 0]) == vertex:
                edge = int(pairs[index, 1])
                assert int(v[edge]) == vertex
                witness.append(edge)
                vertex = int(u[edge])
            del pairs
        witness.reverse()
        assert all(int(v[a]) == int(u[b]) for a,b in zip(witness, witness[1:]))
        witness_deficit = 496*len(witness)-sum(int(weights[e]) for e in witness)
        assert witness_deficit == -int(dist[endpoint])
        if status == 'PASS_FIXED_MEAN_TARGET_OBSTRUCTION':
            assert witness_deficit >= 632 and selected is None
    potential_fields = dict(potential_file=None, potential_sha256=None,
                            potential_archive_sha256=None, minimum_slack=None,
                            all_edge_inequalities_checked=0)
    if selected is not None:
        assert status == 'PASS_MINIMUM_RANGE_AT_MEAN496'
        assert witness_deficit == selected_range
        certificate = scan(selected)
        assert certificate['violation_count'] == 0 and certificate['minimum_slack'] >= 0
        assert int(selected.min()) == 0 and int(selected.max()) == selected_range
        output = run / 'potential.i64.gz'
        potential_raw = selected.astype('<i8').tobytes()
        output.write_bytes(gzip.compress(potential_raw, mtime=0))
        potential_fields.update(potential_file=output.name,
            potential_sha256=hashlib.sha256(potential_raw).hexdigest(),
            potential_archive_sha256=sha(output), minimum_slack=certificate['minimum_slack'],
            all_edge_inequalities_checked=len(weights))
    for relative, digest in prep['input_pins'].items():
        assert sha(R / relative) == digest, relative
    for relative, digest in request['completion_pins'].items():
        assert sha(R / relative) == digest, relative
    result = dict(status=status, graph=build, mean=496, occurrence_credit=0,
        potential_range=selected_range, fixed_mean_minimal=status == 'PASS_MINIMUM_RANGE_AT_MEAN496',
        primary_target='A potential at mean496 with integer range at most631',
        target_met=selected_range is not None and selected_range <= 631,
        target_refuted_at_fixed_mean=status == 'PASS_FIXED_MEAN_TARGET_OBSTRUCTION',
        range_change_from156=None if selected_range is None else selected_range-602,
        certified_range_lower_bound=max(603, witness_deficit or 0),
        comparison=None if selected_range is None else str(Fraction(1098960+8*496+selected_range, 4696)),
        conditional234_margin=None if selected_range is None else 632-selected_range,
        **potential_fields, iterations=iteration, discovery_seconds=discovery_seconds,
        journal_bytes=journal_bytes, journal=layers,
        deficit_walk=[dict(source_edge=int(ids[e]),u=int(u[e]),v=int(v[e]),weight=int(weights[e]),
                           share17_match=bool(retained_matches[e])) for e in witness],
        deficit_walk_value=witness_deficit,
        floors=plan['floors'], pending_floors=plan['pending_floors'],
        inherited_assumptions=plan['inherited_assumptions'],
        preparation_sha256=sha(H/'data/preparation.json'), execution_request_sha256=sha(run/'request.json'),
        completion_pins=request['completion_pins'], input_pins=prep['input_pins'],
        joint_slope_range_optimality=False, new_global_bound=False, Lean_edge_certificate_complete=False,
        scope='Exact finite graph with012034 floor17 and all other inherited conditional premises retained. '
              'A fixed-mean obstruction does not exclude retuned means. No actual-snake upper bound.')
    save(run / 'result.json', result)
    save(progress, dict(phase='FINISHED', worker_pid=os.getpid(), status=status))
    print(json.dumps({key:result[key] for key in ['status','mean','potential_range','target_met',
        'target_refuted_at_fixed_mean','comparison','discovery_seconds','new_global_bound']}), flush=True)


if __name__ == '__main__':
    main()
'''


RUNNER_GATE = r'''
    # The accepted156 receipt and its exact evidence closure must be unchanged.
    completion156_path = R / 'milestones/156-potential-range-and-paper/data/completion.json'
    completion156 = read(completion156_path)
    assert completion156['status'] == 'PASS_SCOPED_JOINT_OPTIMUM_AND_PAPER156'
    assert completion156['fixed_mean_range'] == 602
    assert completion156['equality_parameters'] == {'mean':496,'occurrence_credit':0,'range':602}
    assert not completion156['new_global_bound'] and completion156['unresolved_snake_premises']
    assert not completion156['complete_Lean_graph_certificate']
    oldhome = completion156_path.parent.parent
    for relative, digest in completion156['evidence_sha256'].items():
        assert sha(oldhome / relative) == digest, relative
    for relative, digest in prep['accepted156_pins'].items():
        assert sha(R / relative) == digest, relative
    oldresult = read(oldhome / 'data/share17-range496/result.json')
    oldrun = read(oldhome / 'data/share17-range496/run-status.json')
    assert oldresult['status'] == oldrun['status'] == 'PASS_MINIMUM_RANGE_AT_MEAN496'
    assert oldresult['potential_range'] == oldresult['certified_range_lower_bound'] == 602
    assert oldresult['all_edge_inequalities_checked'] == 4661572
    assert oldresult['minimum_slack'] == 0
'''


def main():
    assert __debug__
    (H / 'scripts').mkdir(exist_ok=True)
    (H / 'data').mkdir(exist_ok=True)
    assert sha(OLD / 'data/preparation.json') == EXPECTED_PREPARATION
    previous = read(OLD / 'data/preparation.json')
    for rel, digest in previous['script_pins'].items():
        assert sha(R / rel) == digest, rel
    completion = read(OLD / 'data/completion.json')
    assert completion['status'] == 'PASS_SCOPED_JOINT_OPTIMUM_AND_PAPER156'
    assert completion['fixed_mean_range'] == 602 and not completion['new_global_bound']
    result = read(OLD / 'data/share17-range496/result.json')
    assert result['status'] == 'PASS_MINIMUM_RANGE_AT_MEAN496'
    assert result['potential_range'] == result['certified_range_lower_bound'] == 602
    assert result['graph'] == read(OLD / 'data/share17-range496/graph-reconstruction.json')
    base_plan = read(R / previous['plan_path'])
    assert sha(R / previous['plan_path']) == previous['plan_sha256']
    plan = {k:base_plan[k] for k in ['original_source_profile','fourteen_cycle','inherited_assumptions']}
    plan.update(status='SOURCE_PREPARED_NOT_EXECUTED',
        floors=dict(result['floors']), pending_floors=dict(result['pending_floors']),
        accepted156_result=(OLD / 'data/share17-range496/result.json').relative_to(R).as_posix(),
        accepted156_graph=(OLD / 'data/share17-range496/graph-reconstruction.json').relative_to(R).as_posix(),
        accepted156_potential=(OLD / 'data/share17-range496' / result['potential_file']).relative_to(R).as_posix(),
        source_plan_path=previous['plan_path'], source_plan_sha256=previous['plan_sha256'],
        primary_target=dict(mean=496, occurrence_credit=0, integer_range_maximum=631),
        witness_checks=dict(original_nine_total=3862, weaker_nine_total=3861,
                            fourteen_total_unchanged=6944, weaker_range_lower_bound=603),
        weight_rule='max(source_weight,120*last_count+max(shape_floor,suffix17))+shared_max_bonus',
        recognition='Suffix six directions and last five counts only, OR forward/reverse; no prefix credit',
        stopping_rule='Stable all-zero relaxation with checked potential, or a checked walk deficit at least632; otherwise unresolved',
        new_global_bound=False, graph_or_Lean_executed_by_preparer=False)
    plan['floors']['012034'] = plan['pending_floors']['012034'] = 17
    write(H / 'data/experiment-plan.json', json.dumps(plan, indent=2)+'\n')
    for name in ['native_resources.py','native_guard.py','reconstruct144.py']:
        write(H / 'scripts' / name, (OLD / 'scripts' / name).read_bytes())
    original_worker = (OLD / 'scripts/potential_range.py').read_text(encoding='utf-8')
    marker = "    save(run / 'graph-reconstruction.json', build)\n"
    assert original_worker.count(marker) == 1
    prefix = original_worker.split(marker)[0]
    prefix = replace_once(prefix, 'SNAKE156_WORKER_PARENT', 'SNAKE157_WORKER_PARENT')
    worker = prefix + WORKER_TAIL
    ast.parse(worker)
    write(H / 'scripts/potential_range.py', worker)
    runner = (OLD / 'scripts/run_potential.py').read_text(encoding='utf-8')
    runner = replace_once(runner, 'experiment after155 completion.', 'experiment after156 completion.')
    runner = replace_once(runner, "default='share17-range496'", "default='floor17-range496'")
    runner = replace_once(runner, "    owned = {os.getpid()}\n", RUNNER_GATE+"    owned = {os.getpid()}\n")
    runner = replace_once(runner, "        completion_pins = dict(complete['source_files_sha256'])\n",
        "        completion_pins = dict(prep['accepted156_pins'])\n"
        "        for relative, digest in complete['source_files_sha256'].items():\n"
        "            assert relative not in completion_pins or completion_pins[relative] == digest\n"
        "            completion_pins[relative] = digest\n")
    runner = replace_once(runner, "floor_profile='full-conditional-plus-suffix17'",
                          "floor_profile='012034-floor17-other-floors-unchanged-plus-suffix17'")
    runner = replace_once(runner, 'SNAKE156_WORKER_PARENT', 'SNAKE157_WORKER_PARENT')
    ast.parse(runner)
    write(H / 'scripts/run_potential.py', runner)

    accepted_pins = {}
    def add(path, expected=None):
        path = Path(path)
        if not path.is_absolute():
            path = R / path
        try:
            relative = path.relative_to(R).as_posix()
        except ValueError:
            relative = str(path)
        digest = sha(path)
        assert expected is None or digest == expected, relative
        assert relative not in accepted_pins or accepted_pins[relative] == digest
        accepted_pins[relative] = digest
    for relative, digest in completion['evidence_sha256'].items():
        add(OLD / relative, digest)
    add(OLD / 'data/completion.json')
    add(OLD / 'data/share17-range496/graph-reconstruction.json')
    add(OLD / 'data/share17-range496' / result['potential_file'], result['potential_archive_sha256'])
    for entry in result['journal']:
        add(OLD / 'data/share17-range496' / entry['path'], entry['sha256'])
    for mapping in [previous['script_pins'],previous['input_pins'],result['completion_pins']]:
        for relative, digest in mapping.items():
            add(relative, digest)
    lean = read(OLD / 'data/range-lean-check.json')
    assert lean['status'] == 'PASS' and lean['exit_code'] == 0 and len(lean['axioms']) == 7
    for mapping in [lean['dependencies'],read(OLD / 'review/walk-audit.json')['input_sha256']]:
        for relative, digest in mapping.items():
            add(relative, digest)
    add(lean['log'], lean['log_sha256'])
    add(lean['object'], lean['olean_sha256'])
    add(R / previous['plan_path'], previous['plan_sha256'])
    add(OLD / 'review/next-step-review.md')
    scripts = ['native_resources.py','native_guard.py','reconstruct144.py',
               'potential_range.py','run_potential.py','prepare_sources.py']
    script_pins = {(H/'scripts'/name).relative_to(R).as_posix():sha(H/'scripts'/name) for name in scripts}
    for name in scripts:
        ast.parse((H/'scripts'/name).read_text(encoding='utf-8'), filename=name)
    preparation = dict(status='SOURCE_PREPARED_NOT_EXECUTED',
        plan_path=(H/'data/experiment-plan.json').relative_to(R).as_posix(),
        plan_sha256=sha(H/'data/experiment-plan.json'), script_pins=script_pins,
        input_pins=accepted_pins, accepted156_pins=accepted_pins,
        original156_script_pins=previous['script_pins'],
        copied_byte_exact=['native_resources.py','native_guard.py','reconstruct144.py'],
        old156_reconstruction_prefix_preserved=True,
        changes=['Reproduce original156 hashes and potential before changing weights',
                 'Lower only012034 shape floor18 to17 inside max; suffix17 and bonuses unchanged',
                 'Record oldpotential failure; remove every602 feasibility shortcut',
                 'Stop on exact feasible range at most631 or a checked walk deficit at least632'],
        resource_limits=dict(startup_free_bytes=3*1024**3,runtime_free_bytes=768*1024**2,
                             owned_private_bytes=3*1024**3,discovery_seconds=600,total_seconds=900,
                             maximum_iterations=1500,journal_bytes=2*1024**3),
        Lean_or_graph_process_started=False, arrays_loaded=False, syntax_checked=True,
        parent_owned_files_preserved=['lean/AffineObstruction157.lean','scripts/check_affine_lean.py',
                                      'data/affine-lean-check.json','data/affine-receipt-recovery.json'])
    write(H/'data/preparation.json', json.dumps(preparation,indent=2)+'\n')
    for relative, digest in previous['script_pins'].items():
        assert sha(R / relative) == digest, relative
    print(json.dumps(dict(status=preparation['status'],scripts=len(scripts),
                          input_pins=len(accepted_pins),preparation_sha256=sha(H/'data/preparation.json'))))


if __name__ == '__main__':
    main()
