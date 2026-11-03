"""Check saved source structure and exact protected inventories; no PDF claim."""
from pathlib import Path
import hashlib, json, re

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
read = lambda p: json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha = lambda b: hashlib.sha256(b).hexdigest()
paper = R / 'paper/snake9_research.tex'
editor = Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
raw = paper.read_bytes()
assert raw == editor.read_bytes()
old = (H / 'audit/paper-before.tex.txt').read_bytes()
s, previous = raw.decode('utf-8'), old.decode('utf-8')
record = read(H / 'data/paper-revision.json')
assert record['status'] == 'PASS_FULL_SOURCE_REVISION_AND_PROTECTED_CONTENT_PRESERVATION'
amendment = read(H / 'data/paper-amendment.json')
assert amendment['status'] == 'PASS_REVIEWED_SINGLE_PHRASE_AMENDMENT'
assert amendment['source_sha256_before'] == record['source_sha256_after']
assert sha(raw) == amendment['source_sha256_after']
pre_amendment = (H / 'audit/paper-before-terminology.tex.txt').read_bytes()
assert sha(pre_amendment) == record['source_sha256_after']
assert pre_amendment.replace(amendment['old_phrase'].encode(), amendment['new_phrase'].encode()) == raw
assert sha(old) == record['source_sha256_before']
assert s.split('\\begin{document}', 1)[0] == previous.split('\\begin{document}', 1)[0]
assert '.lean' not in s
assert s.count('\\begin{definition}') == previous.count('\\begin{definition}') == 1
masked = re.sub(r'\\url\{[^}]*\}', lambda m: m[0].replace('%', 'x'), s)
text = re.sub(r'(?<!\\)%[^\n]*', '', masked)
stack = []
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}', text):
    action, name = m.groups()
    if action == 'begin':
        stack.append(name)
    else:
        assert stack and stack.pop() == name, (name, m.start())
assert not stack
depth = 0
for i, c in enumerate(text):
    if c not in '{}':
        continue
    j = i - 1
    while j >= 0 and text[j] == '\\':
        j -= 1
    if (i - 1 - j) % 2:
        continue
    depth += 1 if c == '{' else -1
    assert depth >= 0, i
assert depth == 0
labels = re.findall(r'\\label\{([^}]+)\}', text)
refs = re.findall(r'\\(?:ref|eqref|pageref|autoref)\{([^}]+)\}', text)
bibs = re.findall(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}', text)
cites = [x.strip() for group in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}', text) for x in group.split(',')]
assert len(labels) == len(set(labels)) and not (set(refs) - set(labels))
assert len(bibs) == len(set(bibs)) and not (set(cites) - set(bibs))
for key in ['formal_statements_exact_multiset_preserved', 'all_display_math_exact_multiset_preserved',
            'witness_quote_blocks_exact_multiset_preserved', 'longtables_exact_multiset_preserved',
            'all_original_labels_and_citation_occurrences_preserved',
            'all_original_bibliography_entries_preserved']:
    assert record['protected_block_inventories'][key], key
prior = R / 'milestones/145-countfree-012301/data/paper-source-review.json'
prior_review = read(prior)
assert prior_review['source_sha256'] == sha(old)
def appendix(x):
    return x.split('\\section{Odd-length witnesses attaining pair sum nine}', 1)[1].split('\\begin{thebibliography}', 1)[0]
assert appendix(s) == appendix(previous)
compile_record = read(H / 'data/paper-compile.json')
assert compile_record['paper_sha256'] == sha(raw)
out = dict(status='PASS_SOURCE_STRUCTURE_AND_PRESERVED_CONTENT', source_sha256=sha(raw),
    preamble_and_authors_unchanged=True, definition_environment_count=1,
    labels=len(labels), references=len(refs), bibliography_entries=len(bibs), citation_occurrences=len(cites),
    balanced_braces_and_environments=True, full_revision=146,
    printed_witnesses_reused=prior_review['printed_witnesses_reused'],
    prior_witness_check_sha256=sha(prior.read_bytes()),
    revision_receipt_sha256=sha((H / 'data/paper-revision.json').read_bytes()),
    amendment_receipt_sha256=sha((H / 'data/paper-amendment.json').read_bytes()),
    pdf_rebuilt=False, visual_layout_checked=False,
    scope='Static source structure, reference resolution and preserved content. The built-in compiler failed before TeX execution.')
(H / 'data/paper-source-review.json').write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps({k: out[k] for k in ['status', 'labels', 'references', 'bibliography_entries', 'citation_occurrences', 'source_sha256']}))
