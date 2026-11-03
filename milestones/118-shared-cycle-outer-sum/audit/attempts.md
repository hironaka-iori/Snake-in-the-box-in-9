# Verification attempts

The first Lean check combined radius-four membership, interior endpoint counts,
component conditions and singleton counts in one statement per forest. It timed
out at 120.438 seconds. No object or theorem success is claimed from that attempt.
Its exact source and checker snapshots, empty log and terminal FAILED record
remain under `logs/`.

The second check shares the concrete vertex data and separates counts from path
components. Radius-four membership and interior endpoints remain Python checks.
The source also includes five coefficient and comparison deductions. All nine
printed axiom reports passed in 30.735 seconds. Only `propext` and `Quot.sound`
appear. The current receipt pins the successful source and object; its snapshot
is distinct from the failed attempt. The final compiler-gate inventory was
saved after the gate passed. Neither existing proof batch was altered.
