# Milestone 158: obstruction to weakening the share floor

Completed. Reducing the uniform 012034 share floor from 18 to 17 prevents
the comparison from falling below 235, even after changing the mean,
potential range and nonnegative uniform occurrence credit.

Read MATHEMATICAL_NOTE.md for the argument and scope. The independently
audited nine-cycle and nine-edge walk give the lower bound 235 + 175/42262.
Six arithmetic statements passed Lean. No unconditional snake bound was
improved.

Authoritative evidence is in data/completion.json, data/floor17-complete,
review/cycle-audit.json and data/floor-lean-check.json. NEXT_STEP.md records
the next local question. Do not restart the prepared milestone-157 test:
the new implementation answers it and establishes a stronger obstruction.

Earlier stopped and failed attempts remain historical records. Version 2
was prepared but never executed. Versions 3 and 4 encountered Windows
record-access races. Version 5 completed after a resource-gated launch and
a later successful attempt. Its retries change record access only.

Source-column copies remain locally in the run directories. They are
excluded from publication because the original hashed archive is already
in the repository and reconstruct_mapped.py recreates them. All non-cache
scripts, receipts, journals, reviews and compiler records are published.

The paper remains at compiled full revision 156. This result is queued for
the next full revision at 166.
