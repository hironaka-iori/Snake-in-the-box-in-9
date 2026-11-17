"""Reuse the accepted publication audit with round-236 evidence fields."""
from pathlib import Path
H = Path(__file__).resolve().parents[1]
previous = (H.parent/'235-joint-two-exchange/scripts/finalize.py').read_text(encoding='utf-8')
prefix = previous[:previous.index('joint = read(')].replace('round 235', 'round 236')
middle = previous[previous.index('archive = read('):previous.index('completion = dict(')]
middle = middle.replace('234-single-colour-exchange/data/completion.json', '235-joint-two-exchange/data/completion.json').replace('after round 235', 'after round 236')
ending = previous[previous.index("save(H / 'data/completion.json'"):].replace('ROUND235', 'ROUND236')
evidence = '''three = read(H / 'data/three-audit.json')
four = read(H / 'data/four-audit.json')
assert three['status'] == four['status'] == 'PASS_DEGREE_MODEL_AUDIT'
assert three['exchanges'] == 3 and three['statuses'] == {'INFEASIBLE': 145}
assert three['models_verified'] == 145 and three['cycle_cuts_verified'] == 0
assert three['all_145_native_excluded'] and not three['unqueried_bases']
assert set(three['covered_bases']) == set(range(145))
assert four['exchanges'] == 4 and four['statuses'] == {'INFEASIBLE': 1, 'UNKNOWN': 3}
assert four['models_verified'] == 4 and four['cycle_cuts_verified'] == 0
for audit in [three, four]:
    assert all(sha(p) == v for p, v in audit['source_and_input_pins'].items())
inverse = read(H / 'data/inverse-audit.json')
assert inverse['status'] == 'PASS_EXACT_Q9_INVERSE' and inverse['entries'] == 262144
assert inverse['entry_counts'] == {'315': 512, '0': 261632}
assert inverse['source_sha256'] == sha(H / 'scripts/verify_inverse.py')
native = []
for tag in ['three', 'three-rest', 'four']:
    e = read(H / 'data' / (tag + '-execution.json'))
    assert e['status'] == 'ACCEPTED_NATIVE_RESULT' and e['exit_code'] == 0 and e['stop_reason'] is None
    assert all(sha(p) == v for p, v in e['pins'].items())
    assert sha(H / 'data' / (tag + '.json')) == e['result_sha256']
    for stream in ['stdout', 'stderr']:
        assert sha(H / 'logs' / (tag + '-' + stream + '.log')) == e[stream + '_sha256']
    native.append(dict(tag=tag, receipt_sha256=sha(H / 'data' / (tag + '-execution.json')), result_sha256=e['result_sha256']))
proofs = []
new_proofs = []
for module, reports in [('ExchangeBalance236', 4), ('AdjacencyInverse236', 2)]:
    a = read(H / 'data' / (module + '-audit.json'))
    assert a['status'] == 'PASS' and a['exit_code'] == 0 and a['stop_reason'] is None and len(a['axioms']) == reports
    new_proofs.append(a)
    proofs.append(dict(module=module, reports=reports, receipt_sha256=sha(H / 'data' / (module + '-audit.json'))))
prior = read(H / 'data/prior-proof-audit.json')
assert prior['status'] == 'PASS_ACCEPTED_PROOF_PINS'
for p in new_proofs + prior['proofs']:
    for pk, hk in [('source', 'source_sha256'), ('object', 'olean_sha256'), ('log', 'log_sha256')]:
        assert sha(p[pk]) == p[hk]
    assert all(sha(path) == digest for path, digest in p['dependencies'].items())
    assert all(set(x['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for x in p['axioms'])
    if 'receipt' in p:
        assert sha(p['receipt']) == p['receipt_sha256']

'''
completion = '''completion = dict(
    round=236, status='PROGRESS', goal_status='PAUSE_REQUESTED_AFTER_PUBLICATION',
    pause_request='Pause the goal after this round finishes and think deeply.', pause_after_round=236,
    started_utc='2026-11-17 15:31:09 UTC', finished_utc=datetime.now(timezone.utc).isoformat(), local_date='2026-11-18',
    interval=[191, 233], new_q9_record=False, new_global_bound=False,
    exact_three_replacement_native_excluded_classes=145, implicit_exchange_descriptions=13879134592000,
    three_models_verified=145, four_models_verified=4, cycle_cuts=0,
    four_excluded=[139], four_unknown=[7, 6, 0], four_unqueried=four['unqueried_bases'],
    maximum_minority_seed_overlap_for_192=92, maximum_seed_overlap_for_192=187,
    minimum_old_vertices_omitted=5, minimum_new_vertices_added=6,
    restricted_one_complete_96_class_at_most_three_exchanges_optimum=191,
    finite_cover_lean_certified=False, native_runs=native, proofs=proofs,
    three_audit_sha256=sha(H / 'data/three-audit.json'), four_audit_sha256=sha(H / 'data/four-audit.json'),
    inverse_audit_sha256=sha(H / 'data/inverse-audit.json'), inverse_entries=262144,
    cube_inverse_lean_instantiation=False, reused_proofs_audit_sha256=sha(H / 'data/prior-proof-audit.json'),
    archive_sha256=archive['archive_sha256'], archived_models=149, documents=docs,
    document_review_sha256=sha(H / 'logs/review-final-documents.md'),
    contributor_revision=contributor, contributor_231_completed=False, independent_233_rebuild=False,
    full_manuscript_review_round=230, next_full_manuscript_review_round=240,
    next_construction='At least four minority replacements; three queried cases unresolved. A generator based on balanced neighbour changes and inverse consistency is proposed but unimplemented.',
    frozen_parent_search_states=previous['frozen_parent_search_states'])
'''
(H/'scripts/finalize.py').write_text(prefix+evidence+middle+completion+ending, encoding='utf-8', newline='\n')
print('PREPARED_ROUND236_FINALIZER')
