# Method limits and endpoint accounting

Checkpoint: 16 October 2026.

Explore the limitation of uniform singleton-density bounds and weighted sharing of endpoint demands. The candidate 1632 singleton count is Python-audited; its connection to the arithmetic lemma is not yet checked in Lean.

Sources and evidence: lean/ResearchDirections.lean; logs/

Paths beginning with `work/`, `outputs/`, or `paper/` are relative to the repository root. Shared proof projects and historical machine data keep stable paths; this folder holds the milestone narrative and new dedicated work.

## Checked reasoning and remaining geometric work

Four abstract statements now pass Lean 4.19.0: the coefficient cap conditional on the witness census, a numerical census showing the limitation of those premises, the weighted endpoint budget, and the five-cycle endpoint-demand contradiction. Their complete axiom audits are in `logs/research-directions-build.log`.

The Python audit in `scripts/audit_density_limit.py` independently verifies bank example 130 and counts 431 empty squares and 1632 singleton squares on 192 vertices. Its result is in `data/density_limit_audit.json`. This census has not yet been connected to the Lean cube definitions.

The proposed next structural experiment is to retain all candidate endpoint sets forced by overlapping low-singleton windows. Search for a family requiring at least three endpoints, including families with no three pairwise disjoint members. Five cyclic pairs give a checked abstract example. First determine whether actual cube geometry can force such a family; the abstract example alone improves no snake bound.

This is an application of standard weighted counting. A limited literature check, including Orland et al., [version 3](https://arxiv.org/html/2607.15270v3), does not establish historical novelty.
