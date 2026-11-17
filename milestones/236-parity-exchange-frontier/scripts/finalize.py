"""Freeze round 236 evidence and prepare the requested paused handover."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
D = Path('D:/Codex/2026-10-13/new-chat/outputs')


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def read(p):
    return json.loads(Path(p).read_bytes())


def save(p, x):
    Path(p).write_text(json.dumps(x, indent=2) + '\n', encoding='utf-8', newline='\n')


three = read(H / 'data/three-audit.json')
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

archive = read(H / 'data/model-archive.json')
assert len(archive['files']) == 149
assert sha(H / 'data' / archive['archive']) == archive['archive_sha256']
assert all(sha(H / 'data' / p) == v['sha256'] for p, v in archive['files'].items())

docs = {}
for name, receipt in [('snake9_frontier_explanation.tex', 'frontier-compile-final.json'),
                      ('snake9_research.tex', 'main-compile-final.json')]:
    p = D / name
    assert p.read_bytes() == (R / 'paper' / name).read_bytes()
    before = (H / 'data' / (name + '.before.txt')).read_text(encoding='utf-8')
    after = p.read_text(encoding='utf-8')
    assert re.search(r'\\author\{[^\n]*', before).group() == re.search(r'\\author\{[^\n]*', after).group()
    if name == 'snake9_research.tex':
        assert re.search(r'\\hypersetup\{.*?\n\}', before, re.S).group() == re.search(r'\\hypersetup\{.*?\n\}', after, re.S).group()
    labels = re.findall(r'\\label\{([^}]+)\}', after)
    assert len(labels) == len(set(labels))
    assert set(re.findall(r'\\label\{([^}]+)\}', before)) <= set(labels)
    assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}', after)) <= set(labels)
    bib = set(re.findall(r'\\bibitem\{([^}]+)\}', after))
    assert {v.strip() for g in re.findall(r'\\cite\{([^}]+)\}', after) for v in g.split(',')} <= bib
    c = read(H / 'data' / receipt)
    assert not c.get('isError', False)
    assert any(json.loads(t['text']).get('kind') == 'success' for t in c['content'] if t['type'] == 'text')
    docs[name] = dict(editor=str(p), mirror=str(R / 'paper' / name), sha256=sha(p),
                      compile_sha256=sha(H / 'data' / receipt))

review = (H / 'logs/review-final-documents.md').read_text(encoding='utf-8')
assert all(x['sha256'] in review for x in docs.values())
assert sha(H / 'MATHEMATICAL_NOTE.md') in review
previous = read(R / 'milestones/235-joint-two-exchange/data/completion.json')
for x in previous['frozen_parent_search_states'].values():
    assert sha(R / x['path']) == x['sha256']
git = ['git', '-c', 'core.commitGraph=false', '-c', 'maintenance.auto=false', '-c', 'gc.auto=0']
contributor = subprocess.check_output(git + ['rev-parse', 'origin/research/unconditional-241'], cwd=R, text=True).strip()
assert contributor == '61e6655e7a8aa16ed6f4f56399c381d753a46f5d'
old = (R / 'README.md').read_text(encoding='utf-8')
assert not old.startswith('# Current result after round 236')

completion = dict(
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
save(H / 'data/completion.json', completion)
save(H / 'data/document-verification.json', dict(documents=docs, scope='Preserved authors, hypersetup, labels and citations; exact mirrors; bounded source review and successful built-in compilation. No full PDF visual review.'))
handoff = (H / 'HANDOFF.md').read_text(encoding='utf-8')
for name in ['CURRENT_STATUS.md', 'NEXT_AGENT_PROMPT.md']:
    (R / 'handoff' / name).write_text(handoff, encoding='utf-8', newline='\n')
(R / 'README.md').write_text((H / 'README_CHECKPOINT.md').read_text(encoding='utf-8') + '\n' + old, encoding='utf-8', newline='\n')
print('FINALIZED_ROUND236; PAUSE_REQUESTED_AFTER_PUBLICATION')
