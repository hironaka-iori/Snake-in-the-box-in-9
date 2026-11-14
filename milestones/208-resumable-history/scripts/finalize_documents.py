"""Record the frozen round and update the existing manuscripts in place."""
from pathlib import Path
import datetime, hashlib, json, subprocess

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
D = Path('D:/Codex/2026-10-13/new-chat/outputs')

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def save(p, value):
    p.write_bytes((json.dumps(value, indent=2) + '\n').encode())

def replace(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError('Expected one manuscript passage: ' + old[:90])
    return text.replace(old, new)

cases = []
for i in [18, 24, 9]:
    folder = H / 'data' / f'case-{i}'
    state = json.loads((folder / 'state.json').read_bytes())
    model = json.loads((folder / 'model.json').read_bytes())
    cases.append({'index': i, 'fixed_coordinates': model['base'],
        'variables': model['variables'], 'status': state['status'],
        'committed_jobs': state['committed_jobs'], 'pending': len(state['frontier']),
        'nodes': state['nodes'], 'solver_seconds': state['seconds'],
        'state': f'data/case-{i}/state.json', 'state_sha256': sha(folder / 'state.json'),
        'model_sha256': sha(folder / 'model.json')})
proof = json.loads((H / 'data/Frontier208-audit.json').read_bytes())
completion = {'round': 208, 'status': 'PROGRESS', 'goal_state': 'ACTIVE',
    'pause_requested': False, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'base_head': subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
    'new_q9_record': False, 'new_global_bound': False,
    'accepted_lean_modules': 1, 'theorem_reports': len(proof['axioms']),
    'proof': {'receipt': 'data/Frontier208-audit.json',
        'receipt_sha256': sha(H / 'data/Frontier208-audit.json'),
        'source_sha256': proof['source_sha256'], 'olean_sha256': proof['olean_sha256'],
        'scope': 'Generic domain split and coverage preservation; concrete native enumeration uncertified.'},
    'six_coordinate_cases': cases, 'exhausted_pairs': 1, 'unresolved_pairs': 27,
    'other_pairs': '25 pairs retain only their round207 initial limited searches.',
    'resource_thresholds': {'startup_free_bytes': 1024**3,
        'reserve_free_bytes': 768*1024**2, 'private_limit_bytes':256*1024**2},
    'limitations': ['Native exhaustion remains outside the Lean proof.',
        'The generic six-changed-history restriction is unchanged.',
        'Single continuation writer; full power-loss durability not established.',
        'A manual per-job STOP marker does not promise whole-batch cancellation.'],
    'contributor_ref': '997f188fc2ca893b4738081943a9f6f32cb11a23',
    'next': 'Continue frozen open frontiers from unchanged copies in the next milestone.'}
save(H / 'data/completion.json', completion)

section = r'''
\subsection{Continuing six-coordinate searches without losing coverage}
\label{sec:history208}
The six-coordinate models retain two indexed histories and allow the
other six coordinates to vary. Their exact pair constraints and global
lexicographic representative conditions are fixed throughout the search.
A restricted branch need not itself be invariant under the residual
coordinate permutations.

\begin{proposition}[Coverage under continuation]
Suppose a list of domain regions covers every acceptable assignment of
a finite model. Replacing one region by regions that cover all its
acceptable assignments preserves this property. A soundly exhausted
region may be removed. If the resulting list is empty, the model has
no acceptable assignment.
\end{proposition}
\begin{proof}
Every acceptable assignment belongs to some old region. If that region
is retained, it remains covered. Otherwise it belongs to one of the
replacement regions by hypothesis. An exhausted region contains no
acceptable assignment. An empty list covers none.
\end{proof}

The required split has an elementary justification. If variable $j$
has domain $D_j$ and $a\in D_j$, replace that domain by either
$\{a\}$ or $D_j\setminus\{a\}$. The two resulting regions are
disjoint and cover the original one. When depth-first search is
interrupted, save the unfinished descendants and the unexamined
remaining-value region at every ancestor. Previously exhausted
children have no acceptable assignment. Induction along the recursion
stack proves coverage of the unfinished part, assuming sound propagation.
All regions are intersected with the same original model conditions.

Lean checks the domain split, disjointness, region replacement and
empty-list implication, in six theorem dependency reports. The native
propagation, recorded branch vectors, concrete model interpretation and
numerical exhaustions remain separate verification obligations.

For the saved 98-edge parent, the model retaining coordinates 1 and 4
now exhausts. Coordinates are zero-based in the saved source. Its 52
interval variables were resolved in 51 committed search steps totaling
1,713,998 nodes. Independent audit of all linked records found a
consistent chain from the root domains to an empty frontier, including
six interrupted refinements and 45 exhausted regions~\cite{research208}.

Thus, at the native-enumeration evidence level, every induced 98-edge
path retaining those two particular indexed histories is cube-isometric
to the source. The general requirement of six changed histories remains
unchanged: the other 27 retained-coordinate pairs are unresolved.
The searches retaining $(0,4)$ and $(3,4)$ have saved open frontiers;
the other 25 pairs retain only their initial limited searches. No new
parent, longer $Q_9$ snake or global numerical bound follows.

'''
mainpath = D / 'snake9_research.tex'
main = mainpath.read_bytes().decode('utf-8')
main = replace(main, 'The first\nsix-coordinate screen reaches its time limits in all 28 cases;\nall remain unresolved and no new parent is found.',
    'The first\nsix-coordinate screen reached its limits in all 28 cases. The\ncontinued calculation below resolves one of those cases.')
marker = r'\section{Construction experiments and their scope}\label{app:experiments}'
main = replace(main, marker, section + marker)
bib = r'''\bibitem{research208}
I. Hironaka, T. Ma and S. Zhan, \emph{Continuing exact coordinate-history
searches with preserved frontier coverage}. Research record 208,
14 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/208-resumable-history}.

'''
main = replace(main, r'\end{thebibliography}', bib + r'\end{thebibliography}')
mainpath.write_bytes(main.encode('utf-8'))

frontpath = D / 'snake9_frontier_explanation.tex'
front = frontpath.read_bytes().decode('utf-8')
front = replace(front, 'Research state after round 207', 'Research state after round 208')
front = replace(front, 'Lean certificate for the concrete searches remains pending. All 28\nsix-coordinate choices reach their initial two-second limits and\nremain unresolved. No new parent is found.',
    'Lean certificate for the concrete searches remains pending. Of the 28\nsix-coordinate choices, one now exhausts and 27 remain unresolved.\nNo new parent is found.')
old = '''The next construction step is to retain unfinished branches of the
six-coordinate models across resource stops. A successful different
parent would still need a separate $Q_9$ joining construction.'''
new = r'''The continuation argument preserves progress across search limits.
For a selected variable with domain $D$ and value $a\in D$, the two
domains $\{a\}$ and $D\setminus\{a\}$ partition its possibilities.
On interruption, retain the unfinished descendants and every ancestor's
unexamined remaining values. Soundly exhausted branches contain no
solution. Induction therefore preserves coverage of all unfinished
assignments. Replacing a covered region by its covering descendants
preserves global coverage; an empty frontier excludes solutions only
when the propagation and exhaustion steps are sound. Lean checks
these generic implications, with six dependency reports.

For this source, retaining coordinate histories 1 and 4 now forces
the original cube-isometry class, at the native-enumeration evidence
level. The search resolves 52 interval variables in 51 committed
steps and 1,713,998 nodes. An independent audit finds the complete
receipt chain consistent. The actual native traversal and concrete
model are still outside the Lean coverage proof.

This excludes one particular pair of retained histories. It does not
raise the general requirement from six changed histories to seven.
The pairs $(0,4)$ and $(3,4)$ have saved unfinished regions, and the
other 25 pairs remain unresolved after their initial limited searches.
Continuing these exact regions is the next step. A successful different
parent would still need a separate $Q_9$ joining construction.'''
front = replace(front, old, new)
front = replace(front, 'research records 175--207.', 'research records 175--208.')
frontpath.write_bytes(front.encode('utf-8'))
for name in ['snake9_research.tex', 'snake9_frontier_explanation.tex']:
    (R / 'paper' / name).write_bytes((D / name).read_bytes())

status = '''# Current state after round 208

The goal remains ACTIVE. The user instructed continued work until she requests a stop. Round 208 is PROGRESS. No new Q9 witness, global numerical bound or optimality proof was obtained; 196 remains unresolved.

Read milestones/208-resumable-history/MATHEMATICAL_NOTE.md and data/completion.json first. Earlier accepted artifacts remain immutable. Round 208 is now frozen for publication; continue from copies in the next milestone.

NEW EXCLUSION: Case 18 retains indexed coordinates [1,4] of the saved 98-edge Q8 source. Its 52-variable six-free-coordinate model exhausts after 51 jobs, 1,713,998 nodes and 41.908 solver seconds. The independent chain audit verifies all 51 authoritative transitions, six LIMIT refinements and 45 EXHAUSTED returns, with no orphan receipt. The conclusion is native finite evidence for this source and retained pair. Other pairs remain unresolved; do not claim a general seven-changed-history restriction.

OPEN FRONTIERS: Case24 retains [0,4], with 100 committed jobs, five pending regions, 3,430,077 nodes and 108.975 solver seconds. Case9 retains [3,4], with 100 jobs, six pending regions, 3,177,434 nodes and 99.188 solver seconds. Both remain OPEN. The other 25 pairs retain their round207 initial LIMIT records. Search sessions5733,63932,71315,98136,60063 are terminal. No native search is active.

LEAN: Frontier208 passes with six dependency reports. It checks domain splitting, disjointness, replacing a region by a covering list, removing an exhausted region under an explicit premise, and the consequence of an empty covered frontier. Concrete native traversal, normalization, pair tables and all numerical exclusions remain outside this generic proof. Do not upgrade a consistent receipt chain to a Lean search certificate.

CONTINUATION: Copy the unchanged scripts continue_search.py, history_solver.c, history_model.py, native_resources.py; build/history_solver.exe; data/lower-dimensional-input.json; and entire data/case-24 and data/case-9 directories (including all linked receipts and states) into the next milestone with the same relative paths. The engine computes its milestone root from its location, so matching bytes retain matching pins. Resume using continue_search.py --indices 24 9 --jobs N --seconds S. To initialize other cases, keep the previous round207 models available. Do not modify the pinned engine or old accepted states. A changed engine requires an explicit, justified frontier transfer.

PERSISTENCE: The old job remains authoritative until the complete replacement state is committed atomically. The global model and lex inequalities never change between subproblems. Single writer only. Manual per-run STOP checkpoints only that invocation and does not promise whole-batch cancellation. Resource-triggered STOP is handled by the wrapper. Full power-loss durability is not established.

RESOURCES: One heavy worker; never compile Lean while native search runs. Keep at least 1 GiB free at startup, 768 MiB reserve and at most 256 MiB private bytes. Lean timeout60s, -j1 -s8192. The bounded55s startup wait does not relax thresholds. Do not kill others' processes. No software tests were created or run.

PRESERVED: Round207 excludes all56 five-coordinate models natively and checks lex reduction plus a concrete reversal obstruction in17 reports. The general source-specific requirement remains at least SIX changed histories at fixed length and index matching. Round206 excludes all70 four-coordinate models. Round205 has659 accepted modules/1543 reports for254 literal finite models and56 active graphs; geometric bridges remain pending. Whole-paper review was200; next is210.

CONTRIBUTOR: Refreshed origin/research/unconditional-241 remains997f188fc2ca893b4738081943a9f6f32cb11a23. Latest previously read report:3120/3127 modules at09:55 UTC14November; no merge or independent rebuild. Archived235 rebuild remains pending;233/234 remain conditional. Fetch named main and research/unconditional-241 only.

DOCUMENTS: The existing D:/Codex/2026-10-13/new-chat/outputs originals are mirrored byte-for-byte in E:/Snake-in-a-box/paper. Preserve authors and hypersetup. Compile frontier first, main last. Consult saved current compilation receipts. Publication uses the round208 exact-byte manifest. Preserve unrelated .gitignore, milestone50 critical-family.json and pre-existing untracked files. Do not run unfiltered git status. Git maintenance/gc/commitGraph stay disabled for publication; bounded pack settings for push.
'''
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:
    (R / 'handoff' / name).write_bytes(status.encode('utf-8'))
readme = R / 'README.md'
lead = '''# Current result after round 208

The six-coordinate model retaining histories 1 and 4 of the saved 98-edge Q8 parent is exhausted in native enumeration. Every target in that fixed indexed family is source-isometric. The other 27 retained pairs remain unresolved, so the general six-changed-history restriction is unchanged. Two open cases have saved continuations.

Lean accepts the generic split and coverage argument with six dependency reports. An independent audit verifies the completed 51-step receipt chain. Concrete search soundness remains outside the Lean proof. No new Q9 witness or global numerical bound is obtained; the goal remains active.

Read [the argument](milestones/208-resumable-history/MATHEMATICAL_NOTE.md), [completion and continuation states](milestones/208-resumable-history/data/completion.json), [chain audit](milestones/208-resumable-history/logs/case18-chain-review.md), [handoff](handoff/CURRENT_STATUS.md), and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''
readme.write_bytes(lead.encode('utf-8') + readme.read_bytes())
publication = H / 'scripts/publication.py'
publication.write_bytes(publication.read_bytes().replace(b'Round207 research artifacts', b'Round208 research artifacts'))
save(H / 'data/document-identities.json', {name: {'editor_source': str(D / name),
    'repository_source': str(R / 'paper' / name), 'sha256': sha(D / name)}
    for name in ['snake9_research.tex','snake9_frontier_explanation.tex']})
print(json.dumps({'cases': cases, 'proof_reports': len(proof['axioms']), 'documents_updated': True}, indent=2))
