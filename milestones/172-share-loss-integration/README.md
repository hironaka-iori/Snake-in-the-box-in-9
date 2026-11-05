# Round172: compatibility checked; share-loss bridge pending

Part1 of the requested three-round continuation172–174.

Compatibility172 passed Lean and checks that the older ShareCharge/SquareIncidence proofs and the new physical loss/domination theorem coexist in one environment. Three printed reports use only standard axioms. Source/object/dependency hashes are pinned. The archived ShareCharge object matches its original proof audit.

ShareLoss172 is a complete proof draft, not yet compiler-checked. It identifies the new emptySquareCount with old emptyAt, selectedNeighborCount with selDeg, and cornerLoss with12e mod d, including d=0. Its intended exact identity is sigma+L=12 totalEmptyAnchored, and its intended physical budget is24T+sigma+840(m+1)+L<=221136. Written reasoning is in review/argument.md.

The compiler startup guard stayed below2GiB on bounded retries; ShareLoss172 was never dispatched. No claim of accepted integration is made. Current startup samples are saved; resource limits were not relaxed. Continue by preparing and running ShareLoss172 using scripts/prepare.py and scripts/check_mathlib.py. Fix compiler errors before accepting it. The two later rounds separately check pure arithmetic, without pretending to establish this missing physical bridge.
