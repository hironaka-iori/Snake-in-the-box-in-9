# Exhaustive search and regrowth certificates

Checkpoint: 16 October 2026.

Integrated GitHub PR 2 at b 0 a 78 f 1. The contributor reports checked regrowth exclusions with 160 and 152 fixed vertices. Broader C searches remain restricted computational results. These do not prove global optimality.

The subsequent KEEP=144 certificate passed Lean 4.19.0 on 16 October 2026:
721 dependency modules, all 262 oriented bank entries, the aggregate theorem,
both-end consequences for every length of at least 192 edges, and a fresh
axiom audit. See [the completion report](lean_completion.md) for the exact
scope, evidence and reproduction commands. KEEP=128, 120 and 112 remain
uncertified; the global optimum is unresolved.

Sources and evidence: work/snake_dfs.c; work/dfs_driver.py; work/final_lean/Dfs*.lean; paper/dfs_report/

Paths beginning with `work/`, `outputs/`, or `paper/` are relative to the repository root. Shared proof projects and historical machine data keep stable paths; this folder holds the milestone narrative and new dedicated work.
