# Milestone 137: twenty-four low-pair windows

The complete actual-snake theorem passed Lean: any snake in Q9 has at most
twenty-four fitting canonical 012032 windows whose second and fourth internal
singleton counts have sum at most nine. Windows may overlap. Every distinct
start is counted once, and there is no path-length parity assumption.

The proof gives twelve windows assigned to a fixed endpoint through the
unselected common neighbour from milestone 134. It constructs the actual
blocks, counts their exceptional prefix only once, subtracts actual missing
pairs from capacity, sums the missing degrees, and handles both exceptional
parameter cases. It then transfers the bound through endpoint normalization,
reversal and halving, and partitions all low-pair starts between endpoints.

Nine Lean modules and twenty-three theorem reports passed. The final module
took 53.156 seconds. All reports use only propext, Classical.choice and
Quot.sound. Failed attempts, exact source snapshots, compiler logs, compiled
objects and dependency hashes are retained. The independent reading found
no mathematical or scope gap in the final source.

The twelve-window assignment premise is the common unselected neighbour.
An arbitrary assignment using only two Hamming-distance equalities is broader.
The proposed boundary-free count eleven remains unchecked. No witness attaining
twelve or twenty-four, and no improved upper bound on total snake length,
is asserted. The recorded interval remains 191–235 with the documented
incomplete independent rebuild of the contributor upper proof. The optimum
and 196 remain open.

The existing paper received a targeted update with the completed proof.
Authors and the full preamble are unchanged; no named definition was added.
The editor and repository copies match. Source checks pass. The built-in
compiler again failed before TeX execution in its Windows helper, so an
updated PDF and its layout are unverified. Last full revision:136; targeted
update:137; next scheduled full revision:146.

The saved process observation found the milestone115 driver live at 952 of
1397 modules. That separate unfinished proof is not part of this completion.

## Continuation

The fixed uniform-credit comparison cannot improve the global length bound
with an allowance of at least two events. Tightening thirty-two to twenty-four
does not remove this obstruction. The next selected research target is the
other seven-edge cycle saved in milestones131–132, which has no 012032 event.
Test its local configurations for a necessary endpoint condition, starting
with bounded counterexample searches. Keep its first-profile mean 3453/7
distinct from its mean496 under the additional-share profile. Any new local
result must be proved for actual snakes before a global bound is claimed.

MATHEMATICAL_NOTE.md gives the proof. The updated handoff supplies exact paths
and verification boundaries. The complete certificate and saved bytes are
indexed by data/verification.json, checkpoint.json and file-manifest.json.
