# Joint optimality of a slope and a potential range

This note concerns the three saved weighted finite graphs used by the empty-square charging argument. It does not determine the maximum snake length in the ninth-dimensional cube.

## Definitions

For a directed graph with edge weight $w(e)$, call $(\mu,\pi)$ a **feasible potential pair** if

$$
\mu+\pi(v)\le w(e)+\pi(u)
$$

for every edge $e:u\to v$. All quantities in this note are rational. A **range bound** $\rho$ satisfies $\pi(u)-\pi(v)\le\rho$ for every pair of states. For a finite graph, one may take $\rho=\max\pi-\min\pi$.

The existing global charge budget and an open walk of $m-8$ edges yield the comparison

$$
m\le B(\mu,\rho):=\frac{A+8\mu+\rho}{4200+\mu},\qquad A=1098960,
$$

provided $4200+\mu>0$ and the separate actual-snake and charge hypotheses hold. In this note, $B$ is also studied as an objective on the finite graph without assuming those hypotheses have been discharged.

## Cycle and path certificate

Suppose a nonempty closed walk has mean weight $M$. Summing the edge inequalities around it gives $\mu\le M$ for every feasible potential pair.

Suppose an open walk has $k$ edges and total weight $C$. Summing along it gives

$$
k\mu-C\le\pi(u_0)-\pi(u_k)\le\rho.
$$

The number $k\mu-C$ is the **path deficit**. If a feasible baseline potential has slope $M$ and range $R=kM-C$, the same path proves that $R$ is the least possible range at that slope.

There is a stronger joint conclusion. Put

$$
B_*:=\frac{A+8M+R}{4200+M}.
$$

Assume $4200+M>0$ and $k+8\le B_*$. For every feasible competing slope and range with $4200+\mu>0$,

$$
\begin{aligned}
A+8\mu+\rho-B_*(4200+\mu)
&\ge A-C+(k+8)\mu-B_*(4200+\mu)\\
&=(k+8-B_*)(\mu-M)\\
&\ge0.
\end{aligned}
$$

Both factors in the last product are nonpositive. Dividing by the positive denominator proves $B(\mu,\rho)\ge B_*$. Thus the baseline is optimal jointly in slope and global potential range for this graph, weight function and boundary budget.

The short-path condition is equivalent to $A-C-4200(k+8)\ge0$. This proof requires neither a shortest path nor realizability of the displayed walk by an actual snake. Realizability becomes relevant when attempting to remove that walk from a stronger graph model.

## Three concrete certificates

| Weighted profile | $M$ | $k$ | $C$ | Normalized range $R$ | Best comparison $B_*$ | Integer comparison |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Completed local floors | $483$ | $9$ | $3796$ | $551$ | $157625/669$ | $235$ |
| Additional assumed 012034 floor 20 | $9259/19$ | $31$ | $14512$ | $11301/19$ | $20965613/89059$ | $235$ |
| Full conditional floors | $496$ | $7$ | $2872$ | $600$ | $137941/587$ | $234$ |

The respective closed-walk lengths are 4, 19 and 3, with weights 1932, 9259 and 1488. The three values of $A-C-4200(k+8)$ are 1023764, 920648 and 1033088. All are positive.

The stored potentials satisfy every one of the 4,947,008 edge inequalities in each pinned array graph. Each supplied open walk follows tight edges from a maximum of the potential to a minimum. Every witness full key $(d,q,c)$ is also accepted by the saved diagram. Exact integer checks and an independent implementation agree on the endpoints, weights, deficits and fractions.

## What has been checked

`lean/PotentialComparison.lean` passed Lean 4.19.0 with seven printed theorem audits. It proves rational path telescoping, the deficit inequality, the cycle slope ceiling, the joint comparison, and the three conditional numerical applications. Printed axiom sets are contained in `propext`, `Classical.choice`, and `Quot.sound`. The source uses no admitted proof or native evaluation shortcut. The checker reuses the installed Mathlib build; it does not rebuild that dependency closure.

The concrete graph witnesses, full potential tables and weight reconstruction were checked by exact Python arithmetic, including an independent implementation. Their embedding in Lean is still a separate obligation. The Lean numerical applications retain the slope ceiling and path-deficit premises explicitly.

Attainment of the displayed optimum is established computationally on the pinned array graphs. Diagram acceptance of the witness keys supplies the necessary constraints for a graph defined from those keys when its weights agree. It does not establish feasibility of the saved potential on any additional diagram-accepted rows. That complete potential check remains required.

## Consequence for further work

Reoptimizing only the constant slope and global potential range on these unchanged weighted graphs cannot sharpen their comparison fractions. Useful changes must affect the optimization problem: stronger verified share credits, additional restrictions justified for actual snakes, a stronger boundary budget, or an estimate depending on the actual initial and final states.

The selected continuation is to prove the exact key-dependent credit bound

$$
L(d_r,q_r,c_r)\le\sum_{i=0}^{4}\operatorname{coreShare}(12,p,r+i+4).
$$

The 55 emitted history share rules require complete coverage of compatible eleven-transition words. A stored representative or a shared acceptance class does not supply that coverage. All alternative credits bound the same five-centre total and are combined by a maximum. The independent interface audit records the precise offsets and remaining premises.

The maintained project interval remains $191\le a(9)\le235$ edges. The upper bound relies on the inspected contributor theorem and saved audit; a complete independent rebuild remains pending. The target 234 retains its unfinished local, graph and charge obligations. No conclusion here establishes a snake of 196 edges or its optimality.
