"""Update current navigation after the exact conditional transfer is accepted."""
from pathlib import Path
import json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert read(H/'data/semantics-completion.json')['status']=='PASS_CORE_SEMANTICS_AND_CONDITIONAL_ACTUAL_SNAKE_SHARE16'
assert read(H/'data/paper-source-review.json')['status']=='PASS_TARGETED_PAPER_SOURCE_CHECKS'
update='''# Research update: milestone 150

The 012032 share-16 target now has a count-free numerical certificate:
58,182 deductions and 5,350,080 references. Its retained core uses none
of the added pair-count clauses or variables. All 112 Lean module checks
for the exact clause interpretation and conditional actual-snake transfer
passed. The complete contradiction remains an explicit premise.

The complete numerical transport and its independent audit passed. The
38-module initial-tree and prefix pilot is prepared and uncompiled. The
existing 012301 full replay remains the only active long Lean job; its
same coordinator resumed after this bounded batch. Inspect live progress
before acting. Do not duplicate it or restart the completed 012310 proof.

Read milestones/150-actual-pair-share/MATHEMATICAL_NOTE.md and its exact
checkpoint. Native inputs and packed transport are preserved in verified
archives. Both existing paper copies are updated without new definitions
or preamble changes. The compiler helper still fails before TeX, so no
new PDF is verified. The maintained interval is 191--235, subject to the
contributor independent-rebuild caveat. Conditional 234 retains its other
premises. Goal ACTIVE; last full paper revision 146, next 156.

'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
             'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
    path=R/name;old=path.read_bytes();assert not old.startswith(update.encode())
    path.write_bytes(update.encode()+old)
path=R/'handoff/NEXT_AGENT_PROMPT.md';old=path.read_text(encoding='utf-8-sig')
assert old.startswith('# Continue after milestone 149')
intro='''# Continue after milestone 150

Read milestones/150-actual-pair-share/MATHEMATICAL_NOTE.md and
data/checkpoint.json there. The exact 012032 core interpretation and
conditional actual-snake share-16 transfer passed all 112 checks. The
count-free contradiction still needs its Lean replay. Do not treat the
numerical replay or clause semantics as a completed local theorem.

The same 147 full replay for 012301 remains active. Revalidate coordinator
PID 15228 and session 67526 against current process identity and progress.
Do not launch a duplicate. After it completes, audit its exact receipts
and run the guarded 148 final composition. The next new 012032 task is
the prepared 38-module pilot. Serialize compilers; do not generate or
launch its full replay until the initial-tree and prefix pilot passes.

The stronger count-free 012032 proof supersedes the proposed one-unit
actual-pair allowance as the selected task. The weaker cap14 numerical
certificate and allowance note are retained without a second Lean
pipeline. No new global bound follows. Keep all remaining local, reference
and potential premises visible. Preserve unrelated edits and exact bytes.
The goal remains ACTIVE. Earlier continuation notes below are historical.

'''
path.write_text(intro+old,encoding='utf-8',newline='\n')
# Keep prose readable without altering any path or code span.
for name in ['README.md','MATHEMATICAL_NOTE.md']:
    p=H/name;parts=re.split(r'(`[^`]*`)',p.read_text(encoding='utf-8'))
    for i in range(0,len(parts),2):
        parts[i]=re.sub(r'(?<=[A-Za-z])(?=\d)|(?<=\d)(?=[A-Za-z])',' ',parts[i])
    p.write_text(''.join(parts),encoding='utf-8',newline='\n')
print('Saved milestone150 navigation and continuation instructions.')
