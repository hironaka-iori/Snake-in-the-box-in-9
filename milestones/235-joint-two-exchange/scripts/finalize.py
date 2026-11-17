"""Freeze round 235 evidence and prepare the requested paused handover."""
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


joint = read(H / 'data/joint-audit.json')
degree = read(H / 'data/degree-audit.json')
assert joint['status'] == 'PASS_SAVED_JOINT_MODEL_AUDIT'
assert joint['statuses'] == {'UNKNOWN': 4} and joint['witness'] is None
assert degree['status'] == 'PASS_DEGREE_MODEL_AUDIT'
assert degree['statuses'] == {'INFEASIBLE': 145}
assert degree['models_verified'] == 145 and degree['cycle_cuts_verified'] == 0
assert degree['all_145_native_excluded'] and not degree['unqueried_bases']
assert set(degree['covered_bases']) == set(range(145))
for audit in [joint, degree]:
    assert all(sha(p) == v for p, v in audit['source_and_input_pins'].items())

native = []
for tag in ['joint', 'degree', 'degree-rest']:
    e = read(H / 'data' / (tag + '-execution.json'))
    assert e['status'] == 'ACCEPTED_NATIVE_RESULT'
    assert e['exit_code'] == 0 and e['stop_reason'] is None
    assert all(sha(p) == v for p, v in e['pins'].items())
    assert sha(H / 'data' / (tag + '.json')) == e['result_sha256']
    for stream in ['stdout', 'stderr']:
        assert sha(H / 'logs' / (tag + '-' + stream + '.log')) == e[stream + '_sha256']
    native.append(dict(tag=tag, receipt_sha256=sha(H / 'data' / (tag + '-execution.json')),
                       result_sha256=e['result_sha256']))

proofs = []
a = read(H / 'data/CircuitPath235-audit.json')
assert a['status'] == 'PASS' and a['exit_code'] == 0 and a['stop_reason'] is None
assert len(a['axioms']) == 4
prior = read(H / 'data/prior-proof-audit.json')
assert prior['status'] == 'PASS_ACCEPTED_PROOF_PINS'
for p in [a] + prior['proofs']:
    for pk, hk in [('source', 'source_sha256'), ('object', 'olean_sha256'), ('log', 'log_sha256')]:
        assert sha(p[pk]) == p[hk]
    assert all(sha(path) == digest for path, digest in p['dependencies'].items())
    assert all(set(x['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for x in p['axioms'])
    if 'receipt' in p:
        assert sha(p['receipt']) == p['receipt_sha256']
proofs.append(dict(module='CircuitPath235', reports=4,
                   receipt_sha256=sha(H / 'data/CircuitPath235-audit.json')))

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
previous = read(R / 'milestones/234-single-colour-exchange/data/completion.json')
for x in previous['frozen_parent_search_states'].values():
    assert sha(R / x['path']) == x['sha256']
git = ['git', '-c', 'core.commitGraph=false', '-c', 'maintenance.auto=false', '-c', 'gc.auto=0']
contributor = subprocess.check_output(git + ['rev-parse', 'origin/research/unconditional-241'], cwd=R, text=True).strip()
assert contributor == '61e6655e7a8aa16ed6f4f56399c381d753a46f5d'
old = (R / 'README.md').read_text(encoding='utf-8')
assert not old.startswith('# Current result after round 235')

completion = dict(
    round=235, status='PROGRESS', goal_status='PAUSE_REQUESTED_AFTER_PUBLICATION',
    pause_request='Pause after this round finishes.', pause_after_round=235,
    started_utc='2026-11-17 12:03:09 UTC', finished_utc=datetime.now(timezone.utc).isoformat(),
    interval=[191, 233], new_q9_record=False, new_global_bound=False,
    exact_two_replacement_native_excluded_classes=145, implicit_exchange_descriptions=8410464000,
    degree_models_verified=145, cycle_cuts=0, original_circuit_unknown_queries=4,
    unresolved_degree_classes=[], maximum_minority_seed_overlap_for_192=93,
    maximum_seed_overlap_for_192=188, minimum_old_vertices_omitted=4,
    minimum_new_vertices_added=5, restricted_one_complete_96_class_at_most_two_exchanges_optimum=191,
    finite_cover_lean_certified=False, native_runs=native, proofs=proofs,
    degree_audit_sha256=sha(H / 'data/degree-audit.json'),
    joint_audit_sha256=sha(H / 'data/joint-audit.json'),
    reused_proofs_audit_sha256=sha(H / 'data/prior-proof-audit.json'),
    archive_sha256=archive['archive_sha256'], archived_models=149, documents=docs,
    document_review_sha256=sha(H / 'logs/review-final-documents.md'),
    contributor_revision=contributor, contributor_231_completed=False, independent_233_rebuild=False,
    full_manuscript_review_round=230, next_full_manuscript_review_round=240,
    next_construction='At least three minority replacements using the degree model; not searched. An overlap-maximization variant is only proposed.',
    frozen_parent_search_states=previous['frozen_parent_search_states'])
save(H / 'data/completion.json', completion)
save(H / 'data/document-verification.json', dict(documents=docs, scope='Preserved authors, hypersetup, labels and citations; exact mirrors; bounded source review and successful built-in compilation. No full PDF visual review.'))
handoff = (H / 'HANDOFF.md').read_text(encoding='utf-8')
for name in ['CURRENT_STATUS.md', 'NEXT_AGENT_PROMPT.md']:
    (R / 'handoff' / name).write_text(handoff, encoding='utf-8', newline='\n')
(R / 'README.md').write_text((H / 'README_CHECKPOINT.md').read_text(encoding='utf-8') + '\n' + old, encoding='utf-8', newline='\n')
print('FINALIZED_ROUND235; PAUSE_REQUESTED_AFTER_PUBLICATION')
