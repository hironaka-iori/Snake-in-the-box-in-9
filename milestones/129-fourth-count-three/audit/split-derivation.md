# Actual fourth-count split

Consider an actual snake with a fitting seven-transition window, beginning at
index \(r\), whose canonical transition word is \(0120324\). Assume
\[
\sum_{j=1}^{6}\alpha_{r+j}\leq22.
\]
The checked result from round 125 gives \(\alpha_{r+4}\geq3\). Since the
counts are integers, the two cases
\[
\alpha_{r+4}=3
\qquad\text{and}\qquad
\alpha_{r+4}\geq4
\]
are exhaustive.

In the equality case, the canonical prefix is \(012032\). The previously
checked first/fourth exclusion rules out
\(\alpha_{r+1}\leq2\) together with \(\alpha_{r+4}\leq3\). Hence
\(\alpha_{r+1}\geq3\). The checked pair inequality
\[
\alpha_{r+2}+\alpha_{r+4}\geq8
\]
then gives \(\alpha_{r+2}\geq5\). Subtracting these lower bounds and the
fourth count from the six-count total yields
\[
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}
\leq22-3-5-3=11.
\]

The resulting necessary intervals, in order from position \(r+1\) through
\(r+6\), are:

| Case | First | Second | Third | Fourth | Fifth | Sixth |
|---|---|---|---|---|---|---|
| Fourth count equals 3 | \([3,21]\) | \([5,21]\) | \([1,21]\) | \([3,3]\) | \([1,21]\) | \([1,21]\) |
| Fourth count is at least 4 | \([1,21]\) | \([2,21]\) | \([1,21]\) | \([4,21]\) | \([1,21]\) | \([1,21]\) |

All other interval entries come from the existing actual-snake bounds. The
sum bound 11 is a consequence of the original total bound and the first
row's strengthened intervals. It supplies no additional mathematical
restriction beyond those statements.

## Lean interface and scope

`lean/ActualSplit129.lean` contains five public statements:

- `actual_fourth_split`: the exhaustive equality/inequality split.
- `actual_equality_consequences`: first count at least 3, second count at
  least 5, and the remaining three counts summing to at most 11.
- `actual_equality_bounds`: the first interval row for every actual count.
- `actual_large_bounds`: the second interval row for every actual count.
- `actual_exhaustive_bounds`: a single disjunction combining the two rows,
  with the remaining-three bound attached to the equality branch.

The only hypotheses describe the actual snake, the fitting window, its
canonical shape, the six-count cap, and the appropriate branch when a branch
statement is used. There are no newly assumed local inequalities or new
mathematical definitions. The module imports the checked round-125 actual
interface, which supplies the round-121 pair theorem as well.

No branch is excluded by these statements. A complete exclusion still needs
checked contradiction evidence and its transfer to the actual snake. These
results alone prove neither a six-count floor of 23 nor a new global upper
bound.

## Verification

The module passed its first launched compilation in 19.281 seconds, with all
five public theorem reports. Every report uses only `propext`,
`Classical.choice`, and `Quot.sound`. No admitted statement or native decision
procedure is present. An earlier gated attempt did not launch because three
other Lean processes were active; its record remains saved.

The checker verified every source pin in
`128-coupled-pair/data/next-case-task.json`, the round-125 environment pins,
and the actual-bound source, object, and log before launching Lean. The
successful launch had 1.80 GiB of free physical memory and one other Lean
process. Source, checker, and dependency hashes were verified unchanged after
compilation. The successful module, checker, and evidence are now fixed;
any later semantic bridge belongs in a separate module.

| File or evidence | SHA-256 |
|---|---|
| `lean/ActualSplit129.lean` | `37321b4e57bf50f01464f4c9c6ca846f53480ac0c8cdbdfe134b6e3dbf520fff` |
| `audit/check_actual_split.py` | `0bf577a657e5b71c31395f2f41f98ee3a5d146b0d0df19bf88f5a0bb39c285de` |
| `build-independent/ActualSplit129.olean` | `b98da49f316f3b6cb70140136714f64b9a3da763786c36720c4c4e3f9fb42f14` |
| `logs/actual-split-1793689366716282000/compiler.log` | `c61dc3cfaa718a92b1d8132178a160f8a2231f6b0a37aba61bd98f57cc9044f0` |
| `logs/actual-split-1793689366716282000/record.json` | `c598784795a3ac5a54189f1ef45e85514a119a86443da9ab8088586485cfefb1` |
