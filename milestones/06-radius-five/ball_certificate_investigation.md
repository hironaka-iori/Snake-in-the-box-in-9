# Radius-five Boolean certificate

Checkpoint: 15 October 2026. The current global interval is 191 <= a(9) <= 245 after integrating the collaborator contribution.

## Exact scope

The finite Boolean contradiction has been translated into ordinary Lean proofs. The final core has **567 clauses, 252 Boolean variables, and 398 derived clauses**. It has no auxiliary prefix-counter variables. Its endpoint restrictions concern 33 candidate vertices. This result certifies the explicit formula, not yet the geometric exclusion for all normalized snakes.

The source `work/final_lean/BallCertificate.lean` contains the formula, one proof for each reverse-unit-propagation step, and the final unsatisfiability theorem. The proof generator is untrusted: Lean checks its output. No native evaluation axiom or proof placeholder is used. The standard LRAT checker was not used in the final proof because its implementation did not reduce directly in the kernel in this environment. The exported proof uses elementary Boolean equalities and propositional reasoning instead.

## Geometric obligations

`work/spectral/CycleExclusion.lean` proves that every nonempty finite subset of an induced path has a vertex with at most one neighbor in the subset. Therefore a nonempty set with two distinct internal neighbors at every vertex cannot be contained in a snake. All 41 recorded cycle cuts are checked against this theorem.

`work/final_lean/BallClauseLogic.lean` checks the general degree-at-most-two clause, the exclusion of three distinct endpoints, endpoint degree at most one, and the existence of another selected neighbor when a vertex does not have degree at most one. The neighbor-list forms for internal vertices are also checked. These are the clause families needed for the remaining bridge. An independent Python audit checked all 567 concrete clause shapes against their recorded geometric meaning; its result is `outputs/ball-encoding-audit.json`. This supplementary audit does not replace the Lean interpretation proof.

Still required:

1. Define a Boolean assignment from the vertices and endpoints of a snake and prove that each of the 567 concrete input clauses follows under the normalized local assumptions. Proven generic clause rules and recorded cycle cuts are available, but this complete instantiation is unfinished.
2. Derive the normalized radius-two selection and its internal-vertex premises from a general one-singleton configuration with both endpoints outside radius two. The existing split-arm theorem retains explicit premises.
3. Establish any aggregate consequence needed to improve the global upper bound.

Neither endpoint proximity nor exact optimality is claimed.

## Certificate generation

The first model has 34,227 clauses. A solver-generated LRAT proof reduces by dependency to 718 input clauses and 663 derived clauses. Replacing the relevant prefix-counter constraints with direct endpoint-triple clauses gives a second model of 5,766 clauses. Its independently generated certificate reduces to the final 567-clause core.

The 33 endpoint vertices, in decimal binary encoding, are:

`13, 14, 22, 25, 38, 41, 49, 50, 70, 73, 81, 82, 97, 98, 134, 137, 145, 146, 161, 162, 193, 194, 262, 265, 267, 273, 274, 289, 290, 321, 322, 385, 386`.

The final core has 27 fixed-selection clauses, 161 degree-at-most-two clauses, 47 internal-degree-two clauses, 32 degree-one-implies-endpoint clauses, one endpoint-degree clause, 20 cycle clauses, and 279 endpoint-triple clauses. Clause provenance and the certificate steps are retained in `outputs/ball_direct_core.json`.

## Reproduction

The existing `outputs/ball_certificate_seed.json` preserves all 41 cycle cuts. To regenerate certificates, use CaDiCaL with LRAT support. The Lean 4.19.0 distribution used here includes it. Run from the repository root:

```sh
python work/ball_cnf.py
cadical --lrat --no-binary outputs/ball_certificate.cnf outputs/ball_certificate.lrat
python work/export_ball_lrat.py
python work/reduce_ball_cnf.py
cadical --lrat --no-binary outputs/ball_direct.cnf outputs/ball_direct.lrat
python work/export_ball_lrat.py --prefix outputs/ball_direct --module BallCertificate
```

CaDiCaL returns exit code 20 for UNSAT; this is the expected solver outcome. The first export creates an intermediate proof source, which the final export replaces. Preserve existing outputs before rerunning experiments. The supplied final source can be checked without running a solver:

```sh
cd work/final_lean
lake build
```

The general cycle lemma and all recorded cuts use the pinned mathlib dependency:

```sh
python work/spectral/verify_incidence.py --module CycleExclusion --mathlib-dir /path/to/mathlib
```

The checked formula is the authority for the finite contradiction. The JSON provenance and generation programs do not replace the remaining geometric proof.

## Quantitative consequence to target

The checked arithmetic lemma `upper_250_of_singleton_surplus` states that the existing incidence identity, the corner bound, and the additional premise T+92 >= 2v imply at most 250 edges. A radius-two ball has 46 vertices; two endpoint balls have at most 92. Proving endpoint proximity for every one-singleton vertex would therefore supply a route to the surplus premise, followed by its aggregation in Lean. That premise remains open, so 250 is a conditional target and the established upper bound is still 254.

Integration note: the unconditional 245-edge bound supersedes the earlier conditional 250 target. The local certificate remains useful as a separate structural investigation; its geometric interpretation remains incomplete.
