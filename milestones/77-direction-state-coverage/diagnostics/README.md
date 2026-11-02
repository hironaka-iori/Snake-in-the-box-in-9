# Superseded proof attempts

These sources and receipts document earlier attempts. They do not determine
the current proof status. Successful current receipts are in `../data/`.

The initial proposition-based direction checks and three monolithic coverage
attempts required excessive memory. The last pruned attempt was stopped after
330 seconds; its Lean process had approximately 20.9 GB of private memory.
No mathematical failure is inferred from an interrupted check.

The boolean direction-table attempt did pass, but its definitions were later
replaced by computed source and target maps. Its receipt is historical.
The current direction definitions and their separate lookup check must be used.

Coverage is now divided at six directions into twelve branches. The largest
branch is split again into seven seventh-direction cases, after its unsplit
attempt reached approximately 9.1 GB of private memory. Every
accepted leaf, rejected branch and assembly step is checked in Lean. The
Python generator supplies source text; its enumeration is not an axiom.

The monolithic lookup-map check was also stopped after its memory use became
excessive. Its replacement checks six consecutive index blocks and joins them
with a proved conjunction identity. The original source and record are saved.

The `history/` folder preserves its own memory-limit, unsupported-option and
source-error diagnostics. Its successful nine-theorem receipt supersedes them.
