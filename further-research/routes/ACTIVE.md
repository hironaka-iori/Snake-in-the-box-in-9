# Active route · One crossing between two eight-dimensional arms

**Continue this route across successive rounds.** Seek a 192-edge snake in the ninth-dimensional cube by placing one induced path in each eight-dimensional face and joining their endpoints across one edge. Fix a long parent and search over the entire other face. Keep the first arm, endpoint orientation, case coverage and strongest checked result identifiable at every pause.

## Why these three length splits suffice

Translate the two joining endpoints to zero in their respective faces. The joined path is induced exactly when the projected arms share only zero. A join with arms of lengths $a,b$ has $a+b+1$ edges. Since each arm has at most 98 edges, any one-crossing path of length at least 192 can be shortened at its free ends to 192 while retaining the crossing. Its unordered arm lengths are then $(96,95)$, $(97,94)$ or $(98,93)$.

## Where to resume after Round 248

1. Start with **donor 15**. The six remaining 96-edge parent indices are **15, 16, 17, 99, 114 and 901** in the frozen Round 246 donor array. For each shape, take both joining endpoints and search for 95 edges in the opposite face. An explicit path or a checked exclusion closes a rooted case. [Parent sequences and indices](../../milestones/248-rooted-arm-capacity/parents.json)
2. Carry unfinished cases forward on the same route. Once the six 96-edge shapes have been addressed, take the three 97-edge donors **18, 19 and 902** and seek 94-edge partners. The displayed 98-edge parent already has a checked exclusion for 93-edge partners. [98-edge ceiling](../../milestones/222-prefix-certificates/MATHEMATICAL_NOTE.md)
3. If this finite collection closes, continue with new 96-, 97- or 98-edge parent shapes. Record how each was generated, identify its class under cube isometries and reversal, and keep both inequivalent joining endpoints. The 15 listed long donor shapes do not exhaust the eight-dimensional cube.

Round 246 compared placements of two specified donor shapes. Round 247 excluded certain middle replacements and solved one intact parent. Round 248 classified the extremal partners of all five intact 96-edge parents represented in the 25 published one-crossing joins. These checked cases are the starting point for the next round. [Round 246](../../milestones/246-eight-dimensional-parents/README.md) · [Round 247](../../milestones/247-relative-middle-placements/README.md) · [Round 248](../../milestones/248-rooted-arm-capacity/README.md)

The [lower-dimensional examples](../../milestones/188-dimensional-constructions/MATHEMATICAL_NOTE.md) illustrate why the crossing count matters. They give explicit compatible pieces for lifts, including a 50-edge path built from three six-dimensional pieces. They supply examples for constructing new parents without imposing a recurrence on the maxima.
