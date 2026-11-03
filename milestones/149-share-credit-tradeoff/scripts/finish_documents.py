"""Save a concise current checkpoint while preserving previous research records."""
from pathlib import Path
H=Path(__file__).resolve().parents[1];R=H.parents[1]
update='''# Research update: milestone 149

On the original 4,947,008-edge share graph, lowering the 012032 floor to 15
cannot be compensated by any uniform occurrence credit. The other eight
floors, event rule and occurrence allowance 24 are fixed. An eleven-cycle,
an unchanged three-cycle and a new 28-edge walk force the comparison to be
at least 235. Five arithmetic statements passed Lean; the exact saved
graph identities were checked separately. This is a limitation of that
specific graph argument, with no new global snake bound.

The 012032 share-16 target remains necessary in this profile. The selected
next step is still the existing 147 full replay, session 67526 and coordinator
PID 15228 at this checkpoint. The same process resumed after the short 149
arithmetic check. Revalidate it before any action; do not restart a live job.
The 148 conditional actual-snake transfer is complete. Its core contradiction
and prepared final composition remain pending.

See milestones/149-share-credit-tradeoff/MATHEMATICAL_NOTE.md and the saved
audit. Both paper copies were updated without new definitions or preamble
changes. PDF preparation still fails in the Windows helper before TeX.
The maintained interval remains 191--235 with the contributor independent
rebuild caveat. Conditional234 retains its other premises. Goal ACTIVE;
last full paper revision146, next156.

'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
             'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
    path=R/name;old=path.read_bytes();assert not old.startswith(update.encode())
    path.write_bytes(update.encode()+old)
path=R/'handoff/NEXT_AGENT_PROMPT.md'
old=path.read_text(encoding='utf-8-sig')
assert old.startswith('# Continue after milestone 148')
intro='''# Continue after milestone 149

Read milestones/149-share-credit-tradeoff/MATHEMATICAL_NOTE.md first. The
fixed-profile floor15/occurrence-credit tradeoff is ruled out for every
credit. The graph identities and arithmetic have separate evidence; no
new global bound is claimed. Do not repeat this failed tradeoff or run the
unnecessary half-credit experiment. Keep the 012032 floor16 target.

The same147 replay remains the selected next task. Its running coordinator
was resumed after149. Everything below concerning that replay and148's
completed conditional transfer remains applicable. The goal is ACTIVE.

'''
path.write_text(intro+old,encoding='utf-8',newline='\n')
print('Saved149 research summaries and continuation instructions.')
