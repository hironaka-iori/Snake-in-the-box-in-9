"""Freeze the completed word-capacity round and its active handoff."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
D = Path('D:/Codex/2026-10-13/new-chat/outputs')

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p, s): p.write_text(s.strip()+'\n', encoding='utf-8', newline='\n')
def save(p, x): write(p, json.dumps(x, indent=2))

assert not (H/'data/history-search.lock').exists()
s = json.loads((H/'data/search-summary.json').read_bytes())
assert s['status'] == 'OPEN'
assert sha(H/'data/case-22/state.json') == s['state_sha256']
proof_path = H/'data/PathWordCapacity215-audit.json'
p = json.loads(proof_path.read_bytes())
assert p['status'] == 'PASS' and p['exit_code'] == 0 and p['stop_reason'] is None
for pk, hk in [('source','source_sha256'), ('object','olean_sha256'), ('log','log_sha256')]:
    assert sha(p[pk]) == p[hk]
for path, digest in p['dependencies'].items(): assert sha(path) == digest
assert len(p['axioms']) == 3
assert all(set(a['axioms']) <= {'propext','Classical.choice','Quot.sound'} for a in p['axioms'])
documents = {}
for name, receipt in [('snake9_frontier_explanation.tex','frontier-compile.json'), ('snake9_research.tex','main-compile.json')]:
    path = D/name
    assert path.read_bytes() == (R/'paper'/name).read_bytes()
    before = (H/'data'/('before-'+name)).read_text(encoding='utf-8')
    after = path.read_text(encoding='utf-8')
    assert re.search(r'\\author\{[^\n]*', before).group() == re.search(r'\\author\{[^\n]*', after).group()
    if name == 'snake9_research.tex':
        assert re.search(r'\\hypersetup\{.*?\n\}', before, re.S).group() == re.search(r'\\hypersetup\{.*?\n\}', after, re.S).group()
    labels = re.findall(r'\\label\{([^}]+)\}', after)
    assert len(labels) == len(set(labels))
    assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}', after)) <= set(labels)
    bib = set(re.findall(r'\\bibitem\{([^}]+)\}', after))
    assert {v.strip() for group in re.findall(r'\\cite\{([^}]+)\}', after) for v in group.split(',')} <= bib
    result = json.loads((H/'data'/receipt).read_bytes())
    assert not result.get('isError', False)
    assert any(json.loads(c['text']).get('kind') == 'success' for c in result['content'] if c['type'] == 'text')
    documents[name] = {'editor':str(path), 'mirror':str(R/'paper'/name), 'sha256':sha(path),
        'compile_receipt':'data/'+receipt, 'compile_sha256':sha(H/'data'/receipt)}
save(H/'data/document-verification.json', {'scope':'Exact mirrors, preserved authors/settings, references and saved compilation success; no page-by-page visual audit.', 'documents':documents})
reviews = ['word-engine-review.md','word-chain-review.md']
assert all((H/'logs'/name).exists() for name in reviews)
assert (H/'data/chain-audit.json').exists()
chain = json.loads((H/'data/chain-audit.json').read_bytes())
assert chain['status'] == 'PASS_SAVED_TRANSFER_AND_NEW_TRANSITIONS'
assert chain['final']['sha256'] == s['state_sha256']
assert chain['new_jobs'] == s['new_jobs']
frozen = {}
for case, folder, jobs, pending, nodes in [('22','214-parity-partner-capacity',240,13,1801017), ('23','211-subset-capacity',296,11,3721372), ('24','209-slice-capacity',150,8,9625900), ('9','209-slice-capacity',150,3,8142891)]:
    path = H.parent/folder/'data'/('case-'+case)/'state.json'
    d = json.loads(path.read_bytes())
    assert d['status'] == 'OPEN' and d['committed_jobs'] == jobs and len(d['frontier']) == pending and d['nodes'] == nodes
    frozen[case] = {'path':str(path.relative_to(R)), 'sha256':sha(path), 'jobs':jobs, 'pending':pending, 'nodes':nodes}
intent = json.loads((H/'data/round-intent.json').read_bytes())
t = s['new_operation_totals']
next_step = (H/'logs/next-step.txt').read_text(encoding='utf-8').strip()
completion = {'round':215, 'status':'PROGRESS', 'previous_goal_turn':'PROGRESS',
    'started_utc':intent['started_utc'], 'utc':datetime.now(timezone.utc).isoformat(),
    'goal_state':'ACTIVE', 'pause_policy':intent['pause_policy'], 'email_sent':False,
    'email_limitation':'No sending connector available.', 'interval':[191,233],
    'contributor_revision':intent['contributor_at_start'], 'contributor_changed':False,
    'independent_233_rebuild':False, 'new_q9_record':False, 'new_global_bound':False,
    'new_six_coordinate_exclusions':0, 'accepted_new_modules':1, 'theorem_reports':3,
    'proofs':[{'module':'PathWordCapacity215','receipt':'data/PathWordCapacity215-audit.json','sha256':sha(proof_path),'reports':3}],
    'search':s, 'frozen_other_states':frozen, 'six_coordinate_unresolved':27,
    'review_hashes':{name:sha(H/'logs'/name) for name in reviews},
    'chain_audit_sha256':sha(H/'data/chain-audit.json'),
    'complete_native_certificate':False, 'complete_normalization_certificate':False,
    'software_tests_created_or_run':False, 'compile_success':True,
    'document_verification':'data/document-verification.json', 'next_step':next_step}
save(H/'data/completion.json', completion)
note = r'''# Round 215: actual-word capacity and partner capacity

The hypothesis was that competition for actual word labels supplies restrictions missed by partner counting alone. The resulting preservation theorem is checked in Lean and used in a separate native search. This is established finite distinct-value reasoning applied to the saved snake geometry; no novelty or speed improvement is claimed.

## Mathematical deduction

Let F be one of the four chosen/outside parity families in the retained(0,6) construction. The actual indexed induced-path condition implies that the assigned words within F are pairwise distinct. Let J be a subset of F and let U contain every current domain of every member of J. Any fitting assignment injects J into U. Therefore

\[
|J|\le |U|.
\]

If equality holds, the assigned words on J occupy all of U. Each other member of F has a different assigned word, so it must avoid U. Deleting U from that member's domain preserves the same complete assignment and hence all path conditions.

This argument requires current-domain fitting, the family/subset premises and the stated containment/cardinality. It needs neither normalization at zero nor a raw-value bound, a fixed parity-pool size, or saturation of all32 words. Raw integer distinctness follows from the path even when the six-bit decoder is not globally injective: equal raw values always decode equally, which contradicts the derived geometric distinctness. The native six-bit masks still have their separate interpretation requirements.

One new module, PathWordCapacity215, passes with three theorem-dependency reports, using only propext, Classical.choice and Quot.sound. It obtains the four literal families' distinctness from round213, then composes the deficient-pool and tight-filter arguments from round211. Complete arbitrary-input normalization, native domain-mask interpretation and traversal certification remain separate.

## Native use

The new engine applies distinct-word capacity separately to each chosen and outside family, then invokes the existing tight-partner rule. A matching proposes subsets. Every failed matching is followed by an actual deficient-union count. Before deleting a tight union, the current domains are recomputed and their union cardinality checked. Earlier deletions can make the stored matching stale, but that matching only proposes a subset; the current union justifies the deduction. Filtering never crosses between the chosen and outside families, since those families can legitimately share words.

A bounded independent source review found no defect under these premises. The source review, finite Lean theorem and saved-transition audit do not constitute kernel certification of the C execution or full search. No software tests were created or run.

The transfer preserves all1448 prior files and all13 unfinished domain vectors. It changes only engine pins and the explicit transfer record. Older source snapshots are preserved; transfer214-state.json and transfer214-initial-state.json identify the newly imported baseline. The frozen round214 state is unchanged.
'''
note += f'''
The continuation accepts {s['new_jobs']} new jobs, visits {t['nodes']:,} additional nodes and reports {t['seconds']:.3f} solver seconds. New job outcomes are {s['new_statuses']}. Actual-word capacity records {t['word_subset_removals']:,} removal operations and {t['word_subset_failures']:,} contradiction returns. Tight-partner capacity records {t['partner_tight_removals']:,} removal operations and {t['partner_subset_failures']:,} contradiction returns. These are repeated branch operations, not counts of globally distinct excluded assignments.

The independently audited saved chain remains OPEN at {s['jobs']} total jobs, {s['pending']} pending regions and {s['nodes']:,} cumulative nodes. Final state SHA-256: {s['state_sha256']}. No new parent class, longer snake or complete coordinate-case exclusion was obtained. Only retained[1,4] is exhausted among the28 six-coordinate cases;27 remain unresolved. Other open cases remain frozen at their prior milestones.

## Research conclusion and next step

{next_step}

The recorded interval remains191<=a(9)<=233. The contributor233 theorem is unconditional, with its saved assembly and axiom audit recorded in round213; independent full rebuilding remains pending. No own numerical bound changed. The conjectured196 remains unresolved. The primary-source check saved in logs/parent-literature-check.md found no accessible classification establishing uniqueness of the98-edge parent; absence of such a catalogue in that check is not evidence of uniqueness.

The goal remains ACTIVE. Ordinary progress warrants continuation. A substantial result or prolonged lack of progress in the user's and this agent's own work may trigger the authorized pause; contributor work alone cannot. No email was sent because no sending connector is available. Both existing manuscripts compile, preserve all three authors and local hyperlink settings, and have exact paper mirrors. Last full-paper review210; next scheduled220.
'''
write(H/'MATHEMATICAL_NOTE.md', note)
handoff = f'''# Current state after round 215

Goal ACTIVE. {intent['pause_policy']} No email was sent: no email-sending connector is available.

Read milestones/215-word-partner-capacity/MATHEMATICAL_NOTE.md and data/completion.json. One new Lean module passes with three reports: all four literal families derive distinct raw words from the reconstructed path; deficient domain pools contradict fitting paths; tight pools can be removed from other members of the same family. No zero normalization, fixed parity alphabet or raw-range premise is needed for this implication. Complete native interpretation, arbitrary-input normalization and traversal certification remain separate.

The recorded interval remains191<=a(9)<=233. Contributor b0521e1d and saved audit b65d30ca are unchanged. The233 theorem is unconditional; independent full rebuilding remains pending. No new snake or coordinate-case exclusion was obtained.

| Case | Pair | Saved milestone | Jobs | Pending | Nodes |
|---|---|---|---:|---:|---:|
|22|[0,6]|215-word-partner-capacity|{s['jobs']}|{s['pending']}|{s['nodes']:,}|
|23|[0,5]|211-subset-capacity|296|11|3,721,372|
|24|[0,4]|209-slice-capacity|150|8|9,625,900|
|9|[3,4]|209-slice-capacity|150|3|8,142,891|

Case22 hash: {s['state_sha256']}. Its word_solver engine and complete copied receipt prefix are pinned. The new{s['new_jobs']} transitions and1448 transferred files have a saved-record audit. Only[1,4] is exhausted among28 six-coordinate cases;27 remain unresolved. Native operation counts do not demonstrate a speed gain.

Next: {next_step}

Copy evidence into a new milestone before continuation; never modify frozen215 state or accepted proofs. Verify explicit transfer and exact model/engine pins. Missing states must not be regenerated silently. Keep one heavy worker; startup>=1GiBfree, reserve>=768MiB, private<=256MiB, Lean60s with -j1 -s8192,55s startupwait. Keep assertions enabled and preserve failed attempts. No software tests unless requested. Preserve unrelated .gitignore and milestone50 edits.

Editor originals: D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, with exact paper mirrors and successful round215 compilation. Preserve author order and hypersetup. Last full-paper review210; next scheduled220. Publish only the exact scoped manifest.
'''
write(R/'handoff/CURRENT_STATUS.md', handoff)
write(R/'handoff/NEXT_AGENT_PROMPT.md', handoff)
header = f'''# Current result after round 215

Actual-word subset capacity is now derived from the source-specific induced path and combined with partner capacity. The new native continuation examines {t['nodes']:,} nodes and records {t['word_subset_removals']:,} word-removal operations. Case[0,6] remains open with{s['pending']} regions. No new snake, global bound or complete coordinate-case exclusion is obtained. The recorded interval remains191<=a(9)<=233; the contributor proof's independent full rebuild is pending.

Read [the mathematical argument](milestones/215-word-partner-capacity/MATHEMATICAL_NOTE.md), [evidence](milestones/215-word-partner-capacity/data/completion.json), [handoff](handoff/CURRENT_STATUS.md) and [frontier explanation](paper/snake9_frontier_explanation.tex). The goal remains active under the user's pause policy.

## Earlier checkpoints

'''
old = (R/'README.md').read_text(encoding='utf-8')
assert not old.startswith('# Current result after round 215')
write(R/'README.md', header+old)
write(H/'README.md', '''# Round 215: actual-word capacity and partner capacity

Read MATHEMATICAL_NOTE.md and data/completion.json. The new Lean receipt records three dependency reports. Native source and saved-chain reviews are in logs/. The search remains open; no global bound changes. Both existing manuscripts compile and the goal remains active.
''')
print('FROZEN_ROUND215: one accepted module, three reports; goal ACTIVE')
