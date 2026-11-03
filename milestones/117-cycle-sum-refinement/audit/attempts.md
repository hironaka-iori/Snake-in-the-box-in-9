# Preserved attempts and limits

The initial local probes and their bounded outcomes are all retained in
`data/probes`. UNKNOWN remains unresolved. The successful native contradiction
and its refined proof have separate replay records; neither supplies a complete
Lean local theorem.

The first attempt to check `SumGeometry117` was refused by the local compiler
memory gate because two Lean processes were already running. It launched no
compiler and left its source and checker snapshots in the attempt log.
The second attempt waited for the same gate and then passed with three axiom
reports. Both attempts are retained. The second receipt's stored list of other
processes is the waiting observation; the checker also re-evaluated and asserted
the gate immediately before launching. No existing research batch was stopped,
restarted or changed.

The preparation script produces the initial checker. The saved checker adds
the bounded wait used by the successful second attempt. The exact checker used
for each attempt is retained with its source snapshot and receipt.

Independent graph review verifies the saved cycles, potential bytes and ranges,
rule applicability and arithmetic. It relies on the producer's all-edge checks
for the corresponding lower certificates and performs no new full-edge scan.
