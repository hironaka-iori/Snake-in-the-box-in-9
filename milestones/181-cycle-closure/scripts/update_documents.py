"""Record the completed bounded round without upgrading its evidence level."""
from pathlib import Path
import json
import re
import shutil

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
EDITOR = Path('D:/Codex/2026-10-13/new-chat/outputs')
replay = json.loads((H / 'data/012301-extended-replay.json').read_text())
passed = replay['status'] == 'PASS_FULL_ORDERED_RUP_REPLAY'
old_replays = json.loads((H / 'data/replays.json').read_text())
assert all(x['status'] == 'PASS_FULL_ORDERED_RUP_REPLAY' for x in old_replays)
all_replays = old_replays + ([replay] if passed else [])
lemmas = sum(x['lemmas'] for x in all_replays)
hints = sum(x['hints'] for x in all_replays)
proof_status = (
    'The complete saved proof passes native replay, including the final empty clause.'
    if passed else
    'The saved native refutation awaits replay; its first replay attempt was stopped before reading the proof because available memory was below the fixed startup threshold.'
)

common = r'''\paragraph{Path restrictions for the remaining window.}
The radius-four share-cap-thirteen queries for $012034,012340,012345$
now have complete native proof replays. Every added clause and the final
contradiction were checked against the saved input. This verification
does not yet supply a Lean contradiction proof or the full geometric
interpretation of the encoding.

The original $012301$ relaxation admits a checked selected set with all
five shares zero and zero loss over the window-neighbour set. It has
sixteen induced eight-cycle components and total loss 5922. Hence a
local remainder budget alone does not remove this obstruction; the
configuration does not satisfy the hypotheses of an actual low-loss snake.

In canonical coordinates, the window is $0,1,3,7,15,14,12$. Its endpoints
have common neighbours 4 and 8. A common neighbour of two path vertices
separated by more than two edges cannot belong to an induced path:
its path index would have to differ by one from both indices, forcing
their separation to be at most two. Thus both closing vertices are absent.
Moreover, a six-edge window in a snake of length at least seven extends
at one end. If the window starts after the first path vertex, use its
predecessor; otherwise use the successor of its last vertex. These
two path properties and the canonical exclusions pass Lean checks.

The closing exclusions alone leave a checked assignment with integer
share 6, rational share $52/7$ and window-neighbour loss 5. In that
assignment, the entire window is an isolated seven-vertex component.
Adding the necessary extension condition removes this example. The
resulting share-cap-thirteen query returns a native contradiction.
REPLAY_STATUS
The extension condition is valid for every actual snake of length at
least seven, so it covers all lengths relevant to the upper-bound argument.
The full Lean replay and the transfer from arbitrary coordinates to the
Boolean model remain pending. No unconditional numerical bound follows
from these local computations alone.
'''.replace('REPLAY_STATUS', proof_status)

for filename in ['snake9_research.tex', 'snake9_frontier_explanation.tex']:
    p = EDITOR / filename
    original = p.read_text(encoding='utf-8')
    assert original == (R / 'paper' / filename).read_text(encoding='utf-8'), 'Editor mirror differs'
    backup = H / 'source-before' / filename
    backup.parent.mkdir(exist_ok=True)
    if not backup.exists():
        shutil.copyfile(p, backup)
    text = original
    start = text.index(r'\paragraph{An obstruction to a purely local low-loss proof.}')
    if filename == 'snake9_research.tex':
        end = text.index(r'\section{Remaining requirements for a stronger bound}', start)
    else:
        end = text.index(r'\textbf{6. What is proved, and what remains.}', start)
    text = text[:start] + common + '\n' + text[end:]
    if filename == 'snake9_research.tex':
        old = 'lowers all four pending floors simultaneously to fifteen. No new unconditional numerical length bound is claimed; the'
        new = ('lowers all four pending floors simultaneously to fifteen. Uniform floor\n'
               'fourteen also suffices when total rounding loss is at least two.\n'
               'The remaining hypothetical 235-edge case has loss zero or one.\n'
               'New path restrictions exclude closing vertices and require a local\n'
               'window to extend; they strengthen the native floor-fourteen calculation.\n'
               'The full local Lean certificates remain pending.\n'
               'No new unconditional numerical length bound is claimed; the')
        assert old in text
        text = text.replace(old, new, 1)
        old = ('because $0\\le k(q)\\le d(q)$. Thus a rational-share lower bound of\n'
               'sixteen would imply integer share at least fifteen when $L\\le1$.\n'
               'Establishing that rational lower bound on the required windows is a\n'
               'proposed continuation, not a result of the present computation.')
        new = ('because $0\\le k(q)\\le d(q)$. This bounds the local rounding deficit\n'
               'by the global loss. For the four pending patterns, the sharper\n'
               'incidence argument below reduces the sufficient rational-share\n'
               'target to a strict bound greater than $72/5$ when $L\\le1$.')
        assert old in text
        text = text.replace(old, new, 1)
    else:
        text = text.replace('Research state after round 180: 7 November 2026',
                            'Research state after round 181')
        old = ('Consequently, a rational-share lower bound of sixteen would imply integer\n'
               'share at least fifteen when $L\\le1$. This is the proposed next local\n'
               'proof target. The double-counting deduction is written here; the required\n'
               'rational lower bound remains unproved.')
        new = ('This bounds the local rounding deficit by $L$. The sharper incidence\n'
               'argument below reduces the sufficient rational-share target to a\n'
               'strict bound greater than $72/5$ when $L\\le1$. The double-counting\n'
               'deduction is written here; the required rational lower bound remains unproved.')
        assert old in text
        text = text.replace(old, new, 1)
        text = text.replace('The partial local share replay\n'
                            'still checks only 33,111 of 145,215 deductions and establishes no final\n'
                            'contradiction.',
                            'The older share-eighteen Lean replay\n'
                            'still checks only 33,111 of 145,215 deductions and establishes no final\n'
                            'contradiction. The new floor-fourteen native replays are separate\n'
                            'certificates and do not complete that older Lean replay.')
        text = text.replace('\\item Prove the four floor-fourteen local bounds for the general case,\n'
                            'and discharge every retained count, exclusion and graph-coverage premise.',
                            '\\item Complete the Lean proofs and geometric interpretation of the\n'
                            'four floor-fourteen certificates, and discharge every retained count,\n'
                            'exclusion and graph-coverage premise.')
        text = text.replace('loss-free comparison in Section 4; rational share at least sixteen is\n'
                            'one proposed way to obtain that local bound.',
                            'loss-free comparison in Section 4. A strict rational-share bound\n'
                            'greater than $72/5$ is sufficient when $L\\le1$. Its proof must\n'
                            'retain necessary path restrictions, including extension.')
        text = text.replace('These are outstanding requirements, not completed results. The goal has resumed for three requested rounds. Round 180 is complete;\n'
                            'one further round remains before the requested pause.',
                            'Rounds 179--181 complete the three requested rounds. Research pauses\n'
                            'at this frontier; these outstanding requirements remain unresolved.')
        text = text.replace('research records 175--180.', 'research records 175--181.')
    assert re.findall(r'\\author\{[^\n]*', text) == re.findall(r'\\author\{[^\n]*', original)
    assert re.findall(r'\\hypersetup\{.*?\n\}', text, re.S) == re.findall(r'\\hypersetup\{.*?\n\}', original, re.S)
    p.write_text(text, encoding='utf-8', newline='\n')
    shutil.copyfile(p, R / 'paper' / filename)

status = f'''# Round 181 complete: three requested rounds finished; pause

Rounds 179, 180 and 181 complete the user's three-round instruction. Pause the goal after publication. Do not begin round 182 without a new instruction to resume.

The maintained project interval is 191–235 edges. The archived contributor proof of 235 still lacks a complete independent rebuild. The upper bound 234 remains conditional; 196 remains conjectural, and no new construction exceeds 191.

Round 179 sharpened the local rational-to-integer deficit to at most 2/5 when global loss L=1. For the four pending patterns, rational share strictly greater than 72/5 suffices for integer share at least 15 when L<=1. Equality does not suffice. Lean checks the arithmetic and canonical incidence statements; the written double counting and coordinate transfer must retain their scope.

Round 180 found native floor-14 refutations for 012034, 012340 and 012345. Its original 012301 model has share zero and zero window-neighbour loss, but contains sixteen eight-cycles and has global loss 5922. It is not a snake.

Round 181 checked two actual-snake properties in Lean: a common neighbour of path positions separated by more than two edges is absent, and a six-edge window in a snake of length at least seven extends at one end. Four theorem dependency reports passed across two modules. Canonical closing vertices 4 and 8 must therefore be absent from the 012301 window 0,1,3,7,15,14,12.

Closing exclusions alone still allow a verified model with integer share 6, rational share 52/7, local loss 5 and global loss 64517. Its window is an isolated seven-vertex component, and other components include fifteen eight-cycles. Adding the necessary extension clause gives native UNSAT at cap 13. {proof_status}

The three round-180 refutations now pass full native replay. Across all accepted round-181 replays, {lemmas:,} added clauses and {hints:,} propagation hints were checked, including a final empty clause for each accepted input. Native replay is separate from Lean replay and from the arbitrary-snake interpretation of the Boolean encoding.

The uniform floor-14 retained-graph comparison is 42248m+45L<=9928364. Conditional on its local and graph premises, L>=2 implies m<=234; m>=235 forces m=235 and L in {{0,1}}. Both low-loss cases dominate Q9. At L=1 the unique positive-remainder corner has d=5 and e=3. Neither case is excluded. Uniform floor 15 would yield conditional 234 without a loss premise.

Inherited requirements remain: retained count restrictions, including the hypothetical 0123104 six-count floor 25 under its exact count conditions; 1358 reference entries; 791 context obligations; graph-to-snake coverage; complete Lean finite-edge and local certificates. The older share-18 Lean replay remains at 33,111/145,215 deductions with no final contradiction. Do not confuse it with the new native replays.

Read milestones/181-cycle-closure/README.md and data/completion.json, then the updated main paper and short explanation in paper/. Authors and hypersetup are preserved. The authoritative editor copies remain in D:/Codex/2026-10-13/new-chat/outputs/. Next manuscript-wide review remains round 186. Preserve unrelated .gitignore and milestone-50 edits. All uncompressed proof caches remain local; compressed evidence is included in publication.
'''
(R / 'handoff/CURRENT_STATUS.md').write_text(status, encoding='utf-8')
next_prompt = f'''# Paused after three completed rounds: 179–181

Resume only after an explicit new user instruction. Do not start round 182 automatically.

Read CURRENT_STATUS.md, milestones/181-cycle-closure/README.md and its data/completion.json. The maintained interval is 191–235 with the archived-235 independent-rebuild qualification. No new unconditional bound or longer construction was obtained.

The selected route remains empty-square charging. The new contribution is a necessary extension condition for the 012301 share query. Closing vertices 4 and 8 are excluded by a Lean-checked actual-snake lemma; a second checked lemma forces a six-edge window to extend when m>=7. The closing-only model has share 6 and an isolated window. The extended cap-13 query is UNSAT. {proof_status}

On resumption, prioritize completing the Lean contradiction/semantic chain for the four floor-14 local certificates. The three other patterns have complete native replays. For 012301, use the extended input, not the satisfiable original or closing-only input. Existing source hashes, original inputs, compressed proofs, solver logs, Lean receipts and model reconstructions are saved. Do not replace native verification by an unsupported claim of a universal Lean-checked share theorem.

The next mathematical strengthening is floor 15 in the remaining global loss cases L=0 or1. Rational share >72/5 suffices there by the 2/5 deficit bound. Include actual-path restrictions in any query; a local remainder budget alone admits the original zero-share cycle model. Do not conflate global L<=1 with a local remainder bound. The exceptional remainder may be outside the window. Universal floor 14 and inherited graph/count conditions are still needed before applying 42248m+45L<=9928364.

Native replay used a 1 GiB startup requirement, 256 MiB private-memory cap, 768 MiB free reserve and 240-second limit. The streamed solver used the same memory guard and a 90-second/128 MiB raw-proof limit. The separate full encoder retained its 1.5 GiB startup requirement; its floor-15 attempt did not start. Preserve startup-stop evidence. Never relax memory guards to conceal a resource failure. Confirm prior workers have terminated before restarting any bounded job. The short core Lean profile is unchanged; avoid simultaneous heavy workers.

Preserve the original D: manuscript/editor and its E: mirror, all three authors and hypersetup. Update both documents after new findings; the next full rewrite review is round 186. Check GitHub before new research and publish each completed round. Do not run or create software tests unless explicitly requested. Lean proof checking is authorized. Preserve unrelated .gitignore and milestone-50 changes.
'''
(R / 'handoff/NEXT_AGENT_PROMPT.md').write_text(next_prompt, encoding='utf-8')
readme = R / 'README.md'
old = readme.read_text(encoding='utf-8')
assert old.startswith('# Current result after round180')
cut = old.index('## Earlier checkpoints')
prefix = '''# Current result after round 181

The three requested rounds, 179–181, are complete; research pauses here. The maintained interval remains 191–235 edges, with the archived upper-bound proof's complete independent rebuild pending. No new unconditional numerical bound is claimed.

The low-loss rational-share target is now strictly greater than 72/5. Necessary path restrictions exclude closing vertices and require a six-edge window to extend in a longer snake. These properties pass Lean and strengthen the remaining local floor-14 calculation. Read [round 181](milestones/181-cycle-closure/README.md) for the exact native-replay and Lean evidence status.

The [current handoff](handoff/CURRENT_STATUS.md), [main manuscript](paper/snake9_research.tex) and [short frontier explanation](paper/snake9_frontier_explanation.tex) are updated. The upper bound 234 still requires the unresolved local and retained-graph premises and a resolution of the remaining loss-zero/loss-one cases, or stronger local floors.

'''
readme.write_text(prefix + old[cut:], encoding='utf-8')

completion = {
    'round': 181, 'status': 'COMPLETE_PATH_RESTRICTIONS_AND_NATIVE_CERTIFICATES',
    'requested_rounds_completed': 3, 'requested_rounds_remaining': 0,
    'pause_requested': True, 'Lean_modules': 2, 'Lean_dependency_reports': 4,
    'native_full_replays': [x['shape'] for x in all_replays],
    'replayed_clauses': lemmas, 'propagation_hints': hints,
    'extended_012301_status': replay['status'],
    'universal_local_Lean_share_theorems_complete': False,
    'new_unconditional_bound': False, 'conditional_234_still_pending': True,
    'new_longer_snake': False,
}
(H / 'data/completion.json').write_text(json.dumps(completion, indent=2) + '\n')
print('Updated both editor documents, their mirrors, current handoffs and round completion record.')
