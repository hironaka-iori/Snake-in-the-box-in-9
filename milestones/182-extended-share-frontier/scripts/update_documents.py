"""Update the existing manuscripts and handoff from accepted round evidence."""
from pathlib import Path
import json,re,shutil
H=Path(__file__).resolve().parents[1];R=H.parents[1]
EDITOR=Path('D:/Codex/2026-10-13/new-chat/outputs')

def accepted(name):
    p=H/'data'/(name+'-audit.json')
    return p.exists() and json.loads(p.read_text())['status']=='PASS'

extension_checked=accepted('ExtensionDirection182')
truncation_checked=accepted('ShareTruncation182')
replay=json.loads((H/'data/012301-extended-replay.json').read_text())
assert replay['status']=='PASS_FULL_ORDERED_RUP_REPLAY'
fixed=H/'data/012301-floor15-fixed16.json'
fixed_status=json.loads(fixed.read_text())['status'] if fixed.exists() else 'PREPARED_NOT_RUN'
fixed_replay=json.loads((H/'data/012301-floor15-fixed16-replay.json').read_text())
assert fixed_replay['status']=='PASS_FULL_ORDERED_RUP_REPLAY'
obstruction_checked=accepted('SingleFloorObstruction182')
assert extension_checked and truncation_checked and obstruction_checked
old_pending='The saved native refutation awaits replay; its first replay attempt was stopped before reading the proof because available memory was below the fixed startup threshold.'
native_done=('The complete saved proof now passes native replay, including its final\n'
             'empty clause. All four floor-fourteen inputs therefore have complete\n'
             'native refutation checks.')
lean_sentence=('The degree exclusions and this canonical-window statement pass Lean checks.'
               if extension_checked else
               'The degree exclusions and canonical-window statement have a written proof; their new Lean module remains unchecked.')
new_math=r'''\paragraph{The extension uses an unused coordinate.}
The possible extension can be restricted further. At the endpoint 0,
coordinates 0 and 1 give the existing neighbour 1 or the forbidden vertex 2.
Selecting 2 would give vertex 3 three selected neighbours: 1, 7 and 2.
Coordinates 2 and 3 give the excluded closing vertices 4 and 8.
At endpoint 12, the first four coordinates give 13, 14, 8 and 4.
Here 14 is the existing neighbour, and selecting 13 would give vertex 15
the three selected neighbours 7, 14 and 13. Therefore every external
extension uses a coordinate $a$ with $4\le a<9$.
LEAN_SENTENCE

Permuting the five unused coordinates and, if necessary, reversing the
window reduces the extension to vertex 16 at the first end. The reversal
is normalized by translation by 12 followed by the coordinate swaps
$0\leftrightarrow1$ and $2\leftrightarrow3$. This preserves the five-centre
share sum. The representative extended segment is
$16,0,1,3,7,15,14,12$, with relabelled transition word $0123412$.
The full isometry transfer remains a written argument.

The floor-fifteen query allowing either extension reached its proof-size
limit and gives no conclusion. With the representative extension fixed,
the query excluding share at most fourteen returned a contradiction.
Its complete native proof replay passed. This is stronger local Boolean
evidence for $012301$; its full Lean and geometric interpretation remain
unfinished.

\paragraph{Why this single improvement does not reduce the comparison.}
In the retained profile $(14,15,14,14)$, ordered as
$012034,012301,012340,012345$, the saved nine-edge cycle still has weight
4448: none of its edges has shape $012301$. The saved eight-edge walk
has two such edges, so its weight rises from 3356 to 3358. Direct
reconstruction of the source rows checks both identities. Every mean
and range for this fixed graph must therefore satisfy
\[
9\mu\le4448,\qquad R\ge8\mu-3358.
\]
For $L=1$, these constraints imply
\[
\frac{1098595+8\mu+R}{4200+\mu}
\ge235+\frac{21}{42248}>235.
\]
Lean checks this comparison for arbitrary nonnegative rational parameters
after clearing denominators. The $L=0$ comparison is larger still.
Thus raising only the $012301$ floor to fifteen cannot yield 234 through
the current mean-and-range argument in the two remaining loss cases.
This is an obstruction from saved walks, with no claim that a new
potential attains the displayed lower comparison.
'''.replace('LEAN_SENTENCE',lean_sentence)
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=EDITOR/name;original=p.read_text(encoding='utf-8')
    assert original==(R/'paper'/name).read_text(encoding='utf-8')
    backup=H/'source-before'/name;backup.parent.mkdir(exist_ok=True)
    if not backup.exists():shutil.copyfile(p,backup)
    assert original.count(old_pending)==1
    text=original.replace(old_pending,native_done)
    boundary=(r'\section{Remaining requirements for a stronger bound}' if name=='snake9_research.tex'
              else r'\textbf{6. What is proved, and what remains.}')
    assert text.count(boundary)==1
    text=text.replace(boundary,new_math+'\n'+boundary,1)
    if name=='snake9_frontier_explanation.tex':
        text=text.replace('Research state after round 181','Research state after round 182')
        text=text.replace('Rounds 179--181 complete the three requested rounds. Research pauses\n'
                          'at this frontier; these outstanding requirements remain unresolved.',
                          'Round 182 completes the requested continuation. Research pauses at\n'
                          'this frontier; these outstanding requirements remain unresolved.')
        text=text.replace('research records 175--181.','research records 175--182.')
    assert re.findall(r'\\author\{[^\n]*',text)==re.findall(r'\\author\{[^\n]*',original)
    assert re.findall(r'\\hypersetup\{.*?\n\}',text,re.S)==re.findall(r'\\hypersetup\{.*?\n\}',original,re.S)
    p.write_text(text,encoding='utf-8',newline='\n');shutil.copyfile(p,R/'paper'/name)

status=f'''# Round 182 complete; pause after publication

The user resumed the goal, then requested pausing after this round. Round 182 is complete. Do not start round 183 without a new instruction to resume.

The maintained project interval remains 191–235 edges, with the complete independent rebuild of the archived contributor 235 proof pending. The upper bound 234 remains conditional; no new longer snake is constructed and 196 remains conjectural.

The remaining floor-14 native proof from round 181 now passes full replay: 211,501 clauses and 11,406,626 propagation hints, including the final empty clause. With the three earlier replays, all four floor-14 Boolean inputs have complete native refutations: 650,902 clauses and 33,809,191 hints in total. The complete Lean contradiction and actual-snake interpretation chains are still pending. The older share-18 Lean replay remains at 33,111/145,215 deductions and is separate evidence.

The new geometric deduction is that every 012301 window in a snake of length at least seven extends through one of its five unused coordinates. Vertices 2 and 13 are excluded by degree three at 3 and 15; the other used-coordinate candidates are existing window neighbours or the closing vertices 4 and 8. {lean_sentence}

A written isometry argument reduces to a selected extension at vertex 16: permute unused coordinates; reverse the window if necessary, normalize by XOR with 12 and swaps 0/1, 2/3. The extended transition word becomes 0123412. The complete coordinate-isometry transfer is not newly Lean-checked.

The streamed floor-15 query with either extension reached the 128 MiB raw-proof limit after about87.48seconds, without a conclusion. The fixed-16 representative query returned UNSAT in27.22seconds. Its full native replay passes:100,151clauses and4,348,019propagation hints, including the final empty clause. The original solver record retains its initial replay-pending label; the separate replay receipt supplies the completed verification. The general cap truncation arithmetic passes Lean, without replacing the Boolean-counter semantics.

Raising only012301 to15 in the otherwise uniform14 profile leaves the nine-edge cycle weight4448 unchanged and raises the eight-edge walk weight to3358. Both source-row identities were reconstructed. They force9mu<=4448 and R>=8mu-3358. For L=1, every mean/range comparison is at least235+21/42248, strictly above235; L=0 is larger still. Lean checks the denominator-cleared obstruction. Thus this one local upgrade cannot close the remaining loss cases through the current fixed-graph comparison. No new potential or global scan is claimed. The other floor15 targets, particularly012034, remain relevant.

The comparison remains 42248m+45L<=9928364 under the retained local and graph premises. L>=2 suffices for conditional234; remaining m>=235 forces m=235 and L in{{0,1}}. Those low-loss snakes dominate Q9; at L=1 the unique positive remainder has d=5,e=3. Round179's strict rational-share target >72/5 suffices for floor15 when L<=1, but the rational lower bound is unproved. A local remainder budget alone still admits the original disconnected cycle model.

All inherited graph/count gaps remain: hypothetical 0123104 six-count floor25 under its exact first-count condition, 1358 reference entries, 791 context obligations, geometric coverage and complete Lean finite-edge/local certificates. No native calculation alone discharges these assumptions.

Read milestones/182-extended-share-frontier/MATHEMATICAL_NOTE.md and data/completion.json. The main manuscript and short explanation are updated in the original D:/Codex/2026-10-13/new-chat/outputs files and mirrored to E:/Snake-in-a-box/paper. Author order and hypersetup are preserved. Next manuscript-wide review remains186. Preserve unrelated .gitignore and milestone50 changes. Keep exact source, proof and failed-attempt evidence.
'''
(R/'handoff/CURRENT_STATUS.md').write_text(status,encoding='utf-8')
next_prompt=f'''# Paused after round 182

Resume only after a new user instruction. Read CURRENT_STATUS.md and milestones/182-extended-share-frontier/MATHEMATICAL_NOTE.md first. No round183 has been started.

All four floor-14 native proofs have full contradiction replays. Complete their Lean and geometric interpretation chains before calling the corresponding universal local bounds established. Do not confuse these with the older, still-partial share-18 Lean replay.

The selected route remains empty-square charging. The new exact geometric restriction is that a 012301 window must extend in an unused coordinate when m>=7. Lean status for its new actual-snake module: {extension_checked}. The written symmetry reduction permits the representative selected extension16; the extended transition word is0123412. Its full isometry transfer remains to be checked in Lean.

The unrestricted endpoint-extension floor15 search reached its proof-size cap, with no conclusion. The fixed16 query returned UNSAT and its complete native replay passes:100,151clauses and4,348,019hints. Do not rerun this completed query. Complete its Lean and semantic interpretation, including the written isometry reduction. Preserve stopped attempts and their compressed evidence.

The profile(14,15,14,14) retains the nine-edge cycle weight4448 and has a saved eight-edge walk weight3358. Source rows were reconstructed and Lean checks the resulting lower comparison235+21/42248 for L=1. L=0 is worse. Thus merely retuning this profile cannot close the remaining case. The remaining floor15 targets, especially012034 which occurs six times on that cycle, are a better next strengthening target. No full new potential scan was performed.

The new streamed cap construction removes only the previous cap unit, adds the fifteenth bit for each of35 centre-neighbour occurrences and caps the resulting525 bits at14. Its arithmetic truncation statement passes Lean. The full Boolean-counter interpretation remains pending. Use saved input/semantic hashes and the delta file; do not silently replace an archived input.

The next mathematical target remains floor15, potentially under global L<=1. The rational-share target >72/5 is sufficient by the2/5 rounding bound. Include necessary path restrictions; a local remainder sum<=1 alone does not express global small loss. Retained count/exclusion/graph premises still need to be discharged for any234 claim.

Maintain the existing resource guards: core Lean/replay/streamed solver startup1GiB, private256MiB and free reserve768MiB. Native searches have90-second and128MiB raw-proof limits; native replay has240seconds. The full encoder has a separate1.5GiB startup profile. Do not weaken guards after a stop. Use one heavy worker at a time. Check GitHub before new research and publish each completed round. Preserve all three authors, local hypersetup, original D: editor documents and E: mirrors. Do not run or create software tests unless explicitly requested; mathematical Lean verification is authorized.
'''
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(next_prompt,encoding='utf-8')
p=R/'README.md';old=p.read_text(encoding='utf-8');assert old.startswith('# Current result after round 181')
cut=old.index('## Earlier checkpoints')
p.write_text('''# Current result after round 182

Round182 is complete; research pauses at the user's request. The maintained interval remains191–235 edges, with the archived235 proof's complete independent rebuild pending. No new unconditional numerical bound is claimed.

All four floor-14 Boolean certificates now have complete native refutation replays. A new Lean-checked actual-path deduction restricts the012301 window's extension to an unused coordinate. A representative-extension floor15 query also has a complete native refutation replay; its full Lean and geometric interpretation remain pending. A checked cycle/walk obstruction shows that this single upgrade cannot yet lower the current comparison below235 in the remaining loss cases. Read [the round182 note](milestones/182-extended-share-frontier/MATHEMATICAL_NOTE.md).

The [current handoff](handoff/CURRENT_STATUS.md), [main manuscript](paper/snake9_research.tex) and [short explanation](paper/snake9_frontier_explanation.tex) are updated. The complete Lean local-certificate and inherited graph/count requirements remain open.

'''+old[cut:],encoding='utf-8')
completion={'round':182,'status':'COMPLETE_NATIVE_REPLAY_AND_EXTENSION_REDUCTION',
            'pause_requested':True,'next_round_started':False,'native_floor14_replays_complete':True,
            'new_replayed_clauses':211501,'new_propagation_hints':11406626,
            'ExtensionDirection182_Lean_checked':extension_checked,'ShareTruncation182_Lean_checked':truncation_checked,
            'SingleFloorObstruction182_Lean_checked':obstruction_checked,'Lean_modules':3,'Lean_dependency_reports':9,
            'fixed_extension_floor15_native_replay':'PASS_FULL_ORDERED_RUP_REPLAY',
            'floor15_replayed_clauses':100151,'floor15_propagation_hints':4348019,
            'fixed_extension_floor15_status':fixed_status,'full_isometry_transfer_Lean_checked':False,
            'universal_floor15_established':False,'complete_local_Lean_certificates':False,
            'new_unconditional_bound':False,'new_longer_snake':False}
(H/'data/completion.json').write_text(json.dumps(completion,indent=2)+'\n')
print('Updated manuscripts, mirrors and handoffs with exact round182 evidence status.')
