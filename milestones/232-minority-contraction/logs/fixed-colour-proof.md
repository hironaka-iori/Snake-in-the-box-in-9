Compilation update: all three reports passed the guarded Lean compiler. See data/FixedColour232-audit.json. Preparation statements below are historical.

# Length bound for a fixed complete colour class

`FixedColour232.lean` is prepared source with three intended axiom reports. It has not been compiled. No solver or tests were run. Its sole imported research module is the accepted `AlternatingCounts191`.

The dependency receipt is `PASS`; the current source, object, and compiler-log hashes all matched it. The source hash is `ab94d9f93ec76301f0fe8624c19992e677e2e0b98682c6d56f6f507dc4a82f85`, and the receipt hash is `648a9f0949a20d24a92d9453f8cd82db74d180191aab8ce8587a0e9f5f590fcd`.

For a path of (L) edges, let (f(i)) indicate membership of its (i)-th vertex in one chosen colour class. The explicit sequence premise is

\[
f(i)+f(i+1)=1\qquad(0\leq i<L),
\]

with natural-number values and total colour count (n) on the (L+1) vertices. Pair the first (2k) positions, where (k=\lfloor(L+1)/2\rfloor). The accepted paired-count identity gives exactly (k) chosen-colour vertices in this prefix. If no position remains, (n=k). Otherwise (n=k+f(2k)\geq k). In both cases

\[
L\leq2n.
\]

The Lean statement needs only nonnegative natural values and the adjacent-pair equation. For a nontrivial sequence, that equation already forces the participating values to be zero or one. The length-zero case satisfies the same bound without an additional value restriction.

If length (2n) is excluded separately, integrality yields (L+1\leq2n). For (n=96), the premise (L\ne192) therefore gives (L\leq191). The three proposed exports are the general bound, its strict version, and this numerical specialization.

For the cube application, the actual-path-to-count bridge remains a written argument: coordinate parity changes on each cube edge, so its indicator satisfies the adjacent-pair equation. Path injectivity and the assertion that the path's complete selected colour class equals a particular saved 96-vertex set identify the colour sum with 96. Merely containing that set is insufficient; additional selected vertices of the same parity would change the count.

The exclusion of length 192 is an explicit premise, supplied by the separate fixed-class native exclusion and its coverage audit. It is not proved by this arithmetic module. If an independently verified 191-edge seed has exactly the same complete selected colour class, it supplies attainment. Together these facts establish exact optimum 191 within that fixed-class family. The source neither verifies the seed nor establishes the native exclusion or a bound over other colour classes.
