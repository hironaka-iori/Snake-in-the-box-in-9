# Milestone 136: interval counts and manuscript revision

Four Lean modules passed, with eleven theorem reports. They construct ordered
blocks of window starts, bound the overlap of their covered intervals, apply
the run-length estimate to missing pairs of an actual snake, and count the
available coordinates outside the set of common coordinates. All successful
reports use only the recorded standard axioms. Failed attempts are retained.

The blocks are obtained by joining consecutive starts whose gap is at most
two. Their common coordinate is constant, and different blocks have a gap
of at least three. Maximal intervals in the full snake are unnecessary for
this construction. The complete transfer to the stronger occurrence estimate
still needs the boundary count, the sum over blocks, and the exceptional case.

The checked bound remains sixteen windows per endpoint and thirty-two in
total under the common-neighbour assignment of milestone 135. Twelve and
twenty-four remain pending. This round gives no new global length bound.
The recorded interval remains 191–235, subject to the documented incomplete
independent rebuild of the contributor upper proof. The optimum and 196 are open.

The paper is revised through this round. The existing editor source and the
repository copy are identical. Authors and the complete preamble, including
the hyperlink settings, are preserved. No named mathematical definition was
added. The mathematical review corrections were applied; the final source
checks resolve all references and reconstruct both newly printed witnesses.
The built-in compiler failed before processing TeX because of a Windows helper
restriction. An updated PDF and its layout have therefore not been verified.
The next scheduled full paper revision is 146.

## Saved material

- MATHEMATICAL_NOTE.md explains the checked statements and remaining steps.
- lean/ contains the four checked sources; logs/ retains every exact attempt.
- data/ records receipts, manuscript checks, the checkpoint and file manifest.
- audit/ retains the original paper, revision fragments and review scope.
- scripts/ contains the checks and process-backed observation of longer jobs.

The milestone 115 certificate job remained live at the saved observation,
with 917 of 1397 modules completed. Its incomplete state is kept separate
from the completed results in this round. No duplicate job was started.
