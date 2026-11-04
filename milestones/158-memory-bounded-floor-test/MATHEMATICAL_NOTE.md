# Why the weaker local floor fails

The hypothesis in milestone 157 is refuted. Lowering only the conditional
012034 share floor from 18 to 17 prevents the retained comparison from
certifying 234. This remains true after varying the mean, potential range
and nonnegative uniform occurrence credit.

The original 156 retained weights were reproduced exactly before changing
the floor. The change affects 936,928 retained edges. An exact search found
a 149-edge walk of weight 73,271, whose deficit at mean 496 is 633. An
independent audit recovered its 56 distinct source rows from the original
hashed columns and checked their retention, weights and overlaps.

## A short obstruction

The walk contains the closed nine-edge cycle with source rows

    991858, 1272641, 3005579, 943614, 1340646,
    3609461, 1726634, 487872, 3070840.

Its successive weights are

    376, 736, 497, 372, 737, 256, 376, 736, 376.

Their sum is 4462. The cycle contains no recorded occurrence event, so its
inequalities imply 9mu <= 4462 for every nonnegative uniform credit C.
In particular, no finite-range potential exists at mean 496 for this
profile, regardless of the allowed range.

The earlier nine-edge walk remains present, with total weight 3861 and
zero occurrence events. It gives R >= 9mu - 3861. Consequently, for
nonnegative mu and C,

    (1098960 + 8mu + 24C + R)/(4200 + mu)
        >= 9931745/42262 = 235 + 175/42262 > 235.

This is a lower bound on the comparison, not a claim of attainment. It
rules out recovering the conditional integer conclusion 234 merely by
retuning these parameters under the weakened floor profile.

## Necessary strength of the local floor

If the 012034 floor is a real parameter F >= 17 and all other rules are
unchanged, the cycle contains two affected edges and the earlier walk
contains one. Their inequalities become

    9mu <= 4428 + 2F,        9mu <= 3844 + F + R.

A comparison strictly below 235 then requires F > 1548/89, approximately
17.3933. Thus an integer uniform floor must be at least 18. Floors below
17 cannot help: decreasing edge weights preserves the obstruction from
the floor-17 profile. This is a requirement of this particular comparison
method, not a theorem that every geometric window has share at least 18.

Six Lean statements check the cycle and walk implications, the rational
comparison, strict separation from 235, the parameter threshold and its
integer consequence. Their only axioms are propext, Classical.choice and
Quot.sound. The source-row interpretation is supplied by the independent
native audit; the full graph-to-snake bridge remains a separate obligation.

## Computation and preserved attempts

The successful run used read-only disk-backed source columns, batched bonus
calculation and a single numerical-library thread. Its peak combined owned
private memory was 424,538,112 bytes. It retained a 1 GiB owned-memory cap,
a 2 GiB startup free-memory requirement and a 768 MiB runtime reserve.
The source mask was reused by exact hash; its geometric justification was
not re-proved by the new loader. Original 144 and complete 156 weight checks
gate the floor change.

Earlier attempts are preserved: the initial storage layout hit its private
memory cap; two later attempts encountered transient Windows record-access
errors; another launch stopped before execution for low available memory.
Version 5 adds bounded read and write retries without changing the numerical
algorithm. The successful run is data/floor17-complete. Its certificate
status is PASS_FIXED_MEAN_TARGET_OBSTRUCTION. The subsequent short-cycle
audit and Lean statements establish the stronger all-mean conclusion above.
One Lean attempt stopped for low free memory; a later unchanged-source run
passed all six statements. Historical failure records remain unchanged.

## Scope and next step

No unconditional snake bound was improved. The maintained interval and
conditional 234 obligations retain their existing proof boundaries.
The next useful local question is whether a count-conditioned share-18
bound can strengthen an affected cycle window without requiring a uniform
floor 18. Breaking this cycle alone is necessary for improvement, and is
not sufficient to certify a new potential. See NEXT_STEP.md.

The paper remains at its compiled full revision 156. This result is queued
for the next full revision at 166; no new definitions are needed.
