# Check attempts

Both concrete witness modules passed their first compiler runs. The final
balanced-witness launch was retried after an incorrect Python executable path;
that initial launch started no compiler and changed no source.

The interval check first stopped before compilation because its checker did
not search the Mathlib object directory. A separate checker records that path.
Its next launch was deferred by the memory gate. The first actual compilation
then exposed an unfinished base-case inequality. Its exact source and log are
preserved under `logs/IntervalPacking133-1793713576373557500`. Adding `omega`
after the interval-cardinality simplification closed the goal. The corrected
module passed with two standard-axiom reports. No proof result is inferred
from the unsuccessful or deferred attempts.

The occurrence-arithmetic module passed its first compiler run. It establishes
conditional integer implications and supplies no missing geometric premise.

The three native probes were each run once. The endpoint0 result remains
uncertified UNSAT. The other probes returned concrete paths subsequently
checked in Lean. Their saved models and cycle cuts remain unchanged.
