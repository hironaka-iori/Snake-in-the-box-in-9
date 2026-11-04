# Retuning the comparison while retaining rounding loss

The finite graph test succeeds. On the same retained graph and conditional
floor profile as milestone 158, with the 012034 floor lowered to 17, the least
potential range at mean 4462/9 is 5411/9. This is a native finite-graph result.
It is not an unconditional bound for snakes.

The calculation retains the exact comparison from milestone 163:

\[
(4200+\mu)m\le1098960+8\mu+24C+R-5\sum_q r_{12}(q).
\]

Set \(\mu=4462/9\) and \(C=0\), and assume total rounding loss at least 4.
Multiplying numerator and denominator by9 gives

\[
m\le\frac{9926156+9R}{42262}.
\]

Since \(235\cdot42262=9931570\), strict improvement below 235 requires
\(9R<5414\). The saved nine-edge walk only required \(9R\ge5409\), and
the saved 149-edge walk required \(9R\ge5399\). Neither excluded this test.

The new potential satisfies every one of the 4,661,572 retained inequalities
\(9w(u,v)+p(u)-p(v)\ge4462\), with minimum 0 and maximum 5411. The minimum
edge slack is 0. A 35-edge retained walk has total unscaled weight 16751, so

\[
35\cdot4462-9\cdot16751=5411.
\]

Summing the inequalities along this walk forces every feasible potential to
have range at least 5411. The exhibited potential attains that lower bound.
Thus the range is minimum at this mean; joint optimality over all means
has not been established here.

Under the retained mathematical premises and rounding loss at least 4, the
comparison becomes

\[
m\le\frac{9931567}{42262}=235-\frac{3}{42262}.
\]

For integral edge length this would give \(m\le234\). The total rounding-loss
lower bound4 remains unproved for the relevant snakes. The inherited local
floor assumptions and interpretation of the retained graph also remain
separate obligations. The potential and its inequalities have been checked
with exact native integer arithmetic, not in Lean. The general retained-loss
arithmetic is Lean-checked in milestone 163; the new numerical substitutions
are reserved for milestone 165.

The run reproduced the original 156 graph and its accepted potential before
changing the floor, then reproduced the accepted 158 floor 17 weight hash
before scaling. The 35-edge witness was checked independently by streaming
the original source archive and recomputing its weights with scalar code.
The first startup failed the 2 GiB memory gate without starting a worker.
The second startup passed; the run finished normally with peak owned private
memory 595,468,288 bytes, well below the 1 GiB limit.

## Resume

Use `data/completion.json`, `data/scaled-floor17/result.json`, and
`review/walk-audit.json`. The potential archive is
`data/scaled-floor17/potential.i64.gz`. Reproducible source columns and
iteration journals remain local; their hashes are in the saved receipts.
The next mathematical obligation is a usable lower bound on total rounding
loss, alongside the inherited graph-to-snake obligations. The successful
finite test establishes a potential compatible with every retained edge
at the selected parameters; it does not establish the loss condition.
