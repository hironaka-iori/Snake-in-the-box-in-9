# Milestone 148: actual-snake transfer for the 012301 share target

The forward and reversed actual-snake consequences are checked. Their
remaining mathematical premise is the contradiction of the exact cap-15
core from milestone147. The full replay is still running. No unconditional
share-16 theorem or new global upper bound is claimed.

## Checked statement

Let a snake have vertices \(x_0,\ldots,x_m\), and let \(r+6\le m\).
Suppose its six directions starting at \(r\), read forward or backward and
relabelled by first occurrence, have shape 012301. If the exact local cap-15
core is contradictory, then

\[
\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge16.
\]

The same conclusion is separately checked from the corresponding local
refutation. The five internal singleton counts automatically lie in [0,21].
There is no additional count, parity or endpoint-location premise.

The checked coordinate realization constructs a permutation of the actual
nine coordinates. The reversed case starts at index \(m-r-6\) in the reversed
snake and preserves the sum over the original five internal centres. Thus
the orientation change introduces no extra endpoint or boundary loss.

The implication is conditional: the Boolean core contradiction is an
explicit theorem argument. The native replay is complete, but its entire
Lean replay must finish before that argument can be discharged.

Evidence: [transfer completion](data/transfer-completion.json),
[dependency review](audit/import-review.md),
[successful batch](data/transfer-v4-progress.json).

## Checked dependencies and retained limitations

Sixteen module checks passed, with 27 standard-axiom reports. These comprise
thirteen newly compiled project helpers, two new conditional consequences
and an axiom audit of one reused automaton data object. The previously
checked 147 model and clause-interpretation dependencies are pinned.

The shared local model sources and objects exactly match their historical
versions. The canonical adapter now imports the interval-case tactic
directly; its proof bodies are unchanged and the reduced import passed.

Three attempted rebuilds reached the 3 GiB memory limit. Every failed source,
checker snapshot, compiler log and resource record is retained:

- The older automaton data module is reused after exact source, object, log
  and direct-dependency matching. Its axiom reports were checked again.
  This is inherited compiled evidence, not a fresh rebuild of that table.
- The snake support file retains the exact generic definitions and proofs
  preceding its unrelated 191-edge witness. The complete original source
  and witness remain saved separately.
- The direction support file retains unchanged proof blocks for coordinate
  relabelling, window directions and reversal. It omits old 239 table
  coverage checks and their catalogue consequences, which are unnecessary
  for the specified-shape transfer.

The existing replay coordinator was held while its current checker finished;
the 148 checks then ran alone. The same coordinator was resumed after each
attempt. No accepted 147 source, plan, object or receipt was changed.

The accepted compiler runs total 76.794 seconds and had a maximum sampled
private-memory use of 2,012,512,256 bytes. These figures exclude failed runs,
waiting, preflight checks and previous 147 compilation. Standard Lean and
Mathlib libraries remain trusted with pinned entry artifacts. Reported
axioms are limited to `propext`, `Classical.choice` and `Quot.sound`.

The reused data source, object and provenance record are archived in
[inherited-data.zip](archives/inherited-data.zip). The exact member hashes
are in [the archive receipt](data/inherited-data-archive.json). A new host
must rebuild or restore its dependency objects and account for the saved
absolute paths; this is not a claim of a fresh build on another machine.

## Next action

Inspect the existing147 full replay process before doing anything else.
Its unified execution session is 67526 and its coordinator PID was 15228
when revalidated after the transfer checks. The authoritative live record
is `../147-countfree-clause-semantics/replay/data/full-replay-progress.json`.
Do not start another replay solely because an observation times out.

The final composition source is already saved as `lean/ShareComplete148.lean`.
It is uncompiled and is excluded from the completed theorem claim.
`scripts/check_complete.py ShareComplete148` refuses to invoke Lean until
the full 147 driver records successful completion of all 1789 modules.
After that point, audit the full replay and its final contradiction, check
this composition and inspect its axiom report. Only then update the local
share theorem to unconditional status.

The maintained project interval remains \(191\le a(9)\le235\), with the
complete independent rebuild of the contributor upper proof still pending.
The conditional 234 profile retains its other local-share, reference and
potential-certificate premises. Keep 012032 and 012340 as joint dependencies.
The optimum and 196 remain unresolved. Do not restart the completed 1397-module
012310 count-sum proof or confuse this target with the separate 012034 share-18
replay.

## Paper and goal status

Both existing paper copies now state the checked conditional transfer and
retain the exact core contradiction as the outstanding premise. Authors,
preamble and existing mathematical statements are preserved; no new
definition was introduced. Static source checks pass. The built-in compiler
fails before TeX processing because of its Windows helper configuration.
No new PDF or visual-layout verification is claimed.

Goal ACTIVE. Round 148 is progress. Last full paper revision 146; next 156.
