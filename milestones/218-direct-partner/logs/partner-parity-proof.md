# Checked actual-path parity

`PartnerParity218.lean` imports the accepted `LayerJoining` and `WordParity214` modules. All three exported statements passed Lean4.19.0 on the first attempt. The source was prepared while the native query was active; compilation began only after the parent reported that query terminal and released the compiler slot.

The common premises are an actual93-edge induced path of Boolean words, a fixed common word length, and even parity at its initial vertex. Alternation is derived from the path's adjacency condition and `WordParity214.adjacent_parity`; it is not a premise supplied independently of the path.

The three exported statements are:

- `index_parity`: parity at index \(i\in\{0,\ldots,93\}\) equals the parity of \(i\).
- `last_is_odd`: the last endpoint, at index93, has odd parity.
- `colour_counts`: the list of94 vertex parities has47 true entries and47 false entries.

The first statement uses bounded natural-number induction. The consecutive-edge fact comes from `p.induced`; equal word lengths permit the accepted adjacent-parity theorem. The second statement specializes the last index. The third rewrites the parity list to the94 explicit index parities and uses ordinary kernel `decide` for those two finite counts. No new definitions, general counting framework or native decision call is introduced.

For an eight-dimensional partner, instantiate the common width as8. Injectivity is already part of the actual induced-path premise, so these index counts count distinct path vertices. Translating a Boolean-word theorem to the native integer selection variables still requires the relevant encoding and path-selection correspondence. No concrete check of integer endpoints0 and78 is included in this source. The claim is the necessary odd-endpoint and47-plus47 restriction for an actual path with an even starting vertex, not an accepted property of any solver output.

Accepted evidence:

- Source `lean/PartnerParity218.lean`: SHA-256 `20645c6ab2d5f7925de073ae3347166735ae1e803dc5d560d330d6f8c6bcace4`.
- Object `build/PartnerParity218.olean`: `43d9e28d6984efba5d0b3fd2febd3d9c26f2472b592f4829fc4e03e0198e7414`.
- Receipt `data/PartnerParity218-audit.json`: `0b19cedfd1608e9a911b175b59c772bfa16d15248e312b9749f096cc2e8fe990`.
- Log `logs/PartnerParity218-1794681863842462400/compiler.log`: `aceed4b8d5b7481eacf7167eab525517d6e9daa62493721bcdac97ad477af8b8`.

All three dependency reports contain only `propext`, `Classical.choice` and `Quot.sound`. No failed attempt or source repair was needed. The guarded run took1.077seconds using one compiler with `-j1 -s8192`, a60-second limit,256MiB private-memory ceiling,768MiB free-memory reserve and1GiB startup requirement. Startup free memory was2,500,681,728bytes; minimum sampled free memory was2,491,949,056bytes; maximum sampled compiler private memory was48,168,960bytes. No resource stop occurred. These sampled values do not assert an unsampled exact memory maximum.

The parent was notified immediately after the compiler became terminal. No solver or software tests were run, and no further compiler was launched.
