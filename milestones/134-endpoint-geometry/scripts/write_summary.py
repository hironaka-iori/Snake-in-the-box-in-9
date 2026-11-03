"""Record geometric progress without upgrading the unfinished occurrence bound."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
modules=['CommonNeighbor134','MissingPair134','PairRepresentation134','EndpointReduction134',
 'PairCapacity134','PathBlock134','RunLength134','CoordinateRun134','ActualRunBound134']
for n in modules:
 assert json.loads((H/'data'/(n+'-audit.json')).read_text())['status']=='PASS'
update='''# Research update: milestone 134

The geometric steps behind the endpoint occurrence argument have passed Lean.
A canonical 012032 window whose relevant pair sum is at most nine has four
alternate vertices and one endpoint adjacent to a single unselected vertex.
One normalization is valid for every window assigned to the same endpoint.
Apart from path indices zero and two, the relevant vertices are coordinate
pairs among the eight coordinates different from the first path direction.

Consecutive pairs {a,b}, {a,c} force the intervening triple {a,b,c} and exclude
{b,c} from the entire snake. An actual represented sequence of such pairs has
distinct other coordinates and missing opposite pairs between consecutive
entries. The finite pair count and the corresponding simple-list length
bound have also passed Lean. All successful receipts and failed attempts are
saved, with exact source and dependency hashes.

The full occurrence theorem remains pending. Its proposed limits of twelve
windows per endpoint, eleven without a counted boundary window, and twenty-four
in total remain written bounds whose complete actual-snake Lean proof is
unfinished. Next: construct maximal intervals, check their overlap and boundary
conventions, sum missing degrees, and combine with the checked integer reduction.

No new global upper bound is claimed. The recorded interval remains 191–235,
with the documented incomplete independent rebuild of the contributor upper
proof. Optimality and 196 remain open. Paper revision 126 is unchanged; the
next full revision is due at 136. Ordinary notation is retained, with no new
named mathematical definitions in this round.

'''
for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
 'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/n;old=p.read_text(encoding='utf-8-sig')
 assert not old.startswith('# Research update: milestone 134')
 p.write_text(update+'## Earlier record\n\n'+old,encoding='utf-8',newline='\n')
(H/'README.md').write_text(update.replace('# Research update: milestone 134',
 '# Milestone 134: geometric steps in the endpoint count')+'''## Saved material

- MATHEMATICAL_NOTE.md explains the checked geometric results and remaining gap.
- lean/ contains the nine checked modules.
- data/ contains successful receipts, a checkpoint and the exact file manifest.
- logs/ retains every compiler attempt with its exact source and checker.
- scripts/ verifies sources, dependencies, logs, proof axioms and staged bytes.
- audit/ contains point-in-time observations of longer proof jobs.

The pair-capacity check passed in about 107 seconds but caused substantial
transient memory pressure. Reuse its verified receipt and object; do not repeat
that exhaustive check while other substantial proof jobs are running.
''',encoding='utf-8',newline='\n')
next_prompt='''# Continuation after milestone 134

Work in E:/Snake-in-a-box. Apply the requested research skill. Use ordinary
notation and define only essential quantities used repeatedly. Preserve all
three authors and hyperlink settings. Fetch GitHub each round. Preserve the
unrelated .gitignore and milestone 50 changes. Do not restart live proof jobs.

Read milestone 134/MATHEMATICAL_NOTE.md, its verification receipt and checkpoint,
and milestone 133/audit/occurrence-geometry.md. Nine new modules passed Lean.
Do not repeat the successful finite checks; PairCapacity134 in particular
caused substantial transient memory pressure despite passing.

Checked in 134:
- CommonNeighbor134: actual low-pair window forces one endpoint and four
  alternate vertices adjacent to a common unselected vertex.
- EndpointReduction134 and PairRepresentation134: normalize the chosen endpoint
  once for all assigned windows; all relevant neighbours are coordinate pairs,
  except possible path indices zero and two. The first direction is excluded
  from ordinary pairs.
- MissingPair134: consecutive pairs ab,ac force triple abc and globally exclude bc.
- CoordinateRun134: derive distinctness of other coordinates and missing
  adjacent pairs from an actual sequence of snake vertices, without a Nodup premise.
- PathBlock134, RunLength134 and ActualRunBound134: use those missing pairs
  to bound a represented list by max(1, available outside coordinates) plus
  the number of eligible missing pairs. The finite sets and their membership
  assumptions are explicit; their degree-based sizes still need to be supplied.
- PairCapacity134: the number of pairs incident to a coordinates among eight is
  7a-a(a-1)/2, with exact selected/missing partition and injective vertex coding.

NEXT: complete the actual endpoint-occurrence theorem. Construct maximal
intervals of the sampled even positions and prove the overlap count, including
the unique exceptional pair at index two and the optional boundary endpoint.
Verify the even-index condition. Apply the checked actual run bound with the
missing-pair set incident to used coordinates and excluding the current common
coordinate. Derive its size t-d_u and the outside size 8-a (or 3-s_u in the
exceptional case). Sum these estimates, with repeated common coordinates handled
correctly. Then supply the geometric hypotheses to OccurrenceArithmetic133.

The written inequalities are
W<=7a-a(a-1)/2-t-2k+delta and
W<=k(5-a+t)-t+1+delta when a<=7.
If W>=12+delta they force a=k=5,t=3. The exceptional degree count yields
W+3k<=6a-4+delta. Handle a=8 separately, as the written proof explains.
The integer implications are already checked. The actual interval assembly
and degree sums remain unfinished; do not replace them with more conditional
integer checks. Keep twelve per endpoint and twenty-four total labelled as
written bounds with incomplete Lean checking. Twenty-two additionally requires
a boundary exclusion; the native endpoint-0 UNSAT result is not certified.

The 149- and 133-edge witnesses from 133 refute a uniform pair floor of ten,
even when both counts are at least four. They do not realize the full critical
cycle or decide a length-235-only condition. The fixed uniform-credit limitation
from 132 also remains: an occurrence budget alone does not give a smaller global
length bound. No new record or optimum has been established.

Recorded interval 191–235, with incomplete independent contributor upper-proof
rebuild. Goal remains ACTIVE. Paper revision 126 unchanged, next revision 136.
Read the saved process observation and verify the milestone 115 driver before
any action involving that job. Do not launch a duplicate checker.
'''
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(next_prompt,encoding='utf-8',newline='\n')
print('WROTE_MILESTONE134_SUMMARY_AND_HANDOFF')
