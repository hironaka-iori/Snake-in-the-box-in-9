"""Publish the completed-round summary without changing archived evidence."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
summary = '''# Current result: exact limit of the retained comparison

Milestone156 is complete. The count-conditioned share17 theorem leaves the
minimum potential range at602. The exact retained-graph optimum, allowing
mean, range and nonnegative uniform occurrence credit to vary jointly, is
551765/2348 =235-15/2348. It is attained at mean496, credit0 and range602.
This is a limitation of the specified conditional finite comparison, with
no new arbitrary-snake upper bound.

All4,661,572 retained edge inequalities were checked in exact native
arithmetic. An independent selected-row audit verified the attaining
nine-edge walk and fourteen-edge cycle. Seven Lean arithmetic theorems
checked their implications; a complete Lean graph certificate remains
unfinished. The maintained191--235 interval and conditional234 obligations
retain their documented scope. The optimum of Q9 remains open.

Read milestones/156-potential-range-and-paper/MATHEMATICAL_NOTE.md and
data/completion.json. The full paper revision preserves the original
statements, proofs, mathematics, witness quotations, tables, authors and
preamble. Both existing sources are identical and compiled successfully.
No new definitions were introduced. Next full paper revision:166.

The next investigation checks whether weakening the conditional012034
share floor18 to17 can preserve the conditional234 comparison. First audit
saved deficit walks and cycles; do not repeat full graph optimization if
a surviving witness already rules out the required range below632.

Historical updates follow; their pending statuses describe earlier stages.

'''

def main():
    old = HERE / 'README.md'
    archive = HERE / 'review/source-preparation-readme.md'
    if not archive.exists():
        archive.write_bytes(old.read_bytes())
    old.write_text('''# Milestone156: potential range and paper revision

Completed. The finite comparison has exact joint optimum551765/2348,
attained at mean496, credit0 and range602. No new global snake bound.

Read MATHEMATICAL_NOTE.md for the argument, assumptions and next check.
data/completion.json binds the accepted native, independent-row, Lean and
paper evidence. scripts/complete_checkpoint.py rechecks their hashes and
scope without rerunning the optimizer or Lean compiler.

The native result retains its original fixed-mean scope. The subsequent
selected-row audit and seven Lean arithmetic statements establish the
joint comparison limitation. Their graph inequalities remain explicit
hypotheses; native all-edge verification is a separate certificate.

The original preparation instructions are preserved in
review/source-preparation-readme.md. Accepted run directories and scripts
must remain byte-identical. The full paper revision compiled; a page-by-page
visual review was not performed. Next full revision:166.
''', encoding='utf-8')
    for name in ['README.md', 'handoff/CURRENT_STATUS.md', 'handoff/NEXT_AGENT_PROMPT.md']:
        path = ROOT / name
        raw = path.read_bytes()
        if not raw.startswith(summary.encode('utf-8')):
            path.write_bytes(summary.encode('utf-8') + raw)
    print('Updated milestone README and three current-status headers.')

if __name__ == '__main__':
    main()
