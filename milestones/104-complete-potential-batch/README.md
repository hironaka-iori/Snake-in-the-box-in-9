# Milestone 104: complete potential certificate batch

This milestone is in progress. The live record on the running machine is
`data/batch-progress.json`; the portable record is the
[saved launch snapshot](data/start-checkpoint.json). Generated sources are
proposed certificates. Only successful Lean receipts count as checked work.

The general graph-assembly theorem has passed Lean. It derives the original
graph checker from context certificates for every entry of the existing list
of 791 saved blocks. Missing contexts follow from the existing missing-block
theorem, without enumerating all direction/history combinations again.
This argument adds no definitions.

The full queue contains 1,157 groups covering the 1,570 profile/context pairs
still pending after milestone 103. Identical acceptance roots, potential roots
and reduced weight expressions allow one checked prefix theorem to support
several original contexts. Each context still receives its own Lean theorem.
The six previously checked contexts in each profile are reused in the final
assembly. No accepted edge or context key is removed by this grouping.

The preferred methods are the existing prefix checker for the completed
profile and joint traversal for the conditional profile. This choice follows
the limited comparisons in milestone 103. Each new group has a separate
alternative source using the other method. A timeout permits the alternative;
an ordinary proof error stops the batch for inspection.

The batch runs one Lean compiler at a time. To resume after it stops, inspect
the live record and the processes named in the lock files, then run
`scripts/run_batch.py` with the configured Python runtime. Do not start a
second batch or modify a live proof source or checker. Successful receipts
are verified and reused. Preserve unsuccessful attempts and their exact bytes.

Once every group passes, the driver generates and checks the completed and
conditional graph assemblies. Only those successful final checks justify a
claim that this milestone certifies the complete graph. A final source,
dependency and axiom audit must follow before publishing a completed result.

The maintained project interval remains (191\le a(9)\le235) edges, with 234
conditional. The contributor's 235 result retains its archived audit and
pending independent rebuild. The two reference catalogues and the five
conditional local-share refutations remain separate obligations. The exact
optimum and conjecture 196 are unresolved.

The paper remains revision 96, with the same authors and hyperlink settings.
The next scheduled full revision is 106. No new mathematical terminology is
introduced in this milestone.
