# Round 216 two-step geometry source

Prepared TwoStep216.lean for the parent's Lean check. No compilation, tests, solver, search, or nested delegation was performed. Acceptance and axiom reports remain pending; the source contains no sorry, new axiom, native_decide, or large generated certificate.

The module imports PathParity214 and contains five theorem candidates:

1. `hamming_triangle`: equal-length Boolean lists satisfy the Hamming triangle inequality. The proof uses list induction and the eight Boolean-head cases.
2. `two_step_distance`: when the first and second Hamming distances both equal one, the outer distance is zero or two. The triangle inequality gives an upper bound of two. Two parity flips restore the initial parity, which rules out outer distance one.
3. `two_step_distance_of_ne`: distinct outer words eliminate the zero-distance case.
4. `free_two_step_distance`: for the literal reconstructed induced Q8 path and a group index less than 76, the decoded words at groups g and g+2 have distance zero or two. It applies PathParity214.free_adjacent at g and g+1; the decoded words all have length six.
5. `free_two_step_distance_of_ne`: the same source-specific consequence with outer distance exactly two, assuming the decoded outer words are distinct.

The actual-path premise is precisely the existing IndexedCubePath 8 condition on the two retained base bits followed by the six decoded free bits. No new normalization, raw-word range, or parity-alphabet assumption is added. The source-specific statements concern groups 0 through 77, with g below 76 ensuring both required adjacent-group facts are available.

The zero-distance alternative must remain unless decoded-word distinctness is justified separately. Inequality of unrestricted raw natural numbers does not suffice, because the decoder reads only six bits. No decoder injectivity lemma or claim that every pair of groups two steps apart has distinct free words is introduced.

The parent owns the general triple-domain support-preservation statement, which is intentionally absent from this module. These geometric statements do not certify native support masks, exhaustive traversal, general source normalization, or any global Q9 bound.

SHA-256 snapshots:

- `216-joint-word-support/lean/TwoStep216.lean`: `9bb2e7c990bcc91360bc0f25a73cabedb906d9574f492d501eb08ff850309b2a`
- `214-parity-partner-capacity/lean/PathParity214.lean`: `88a607ae0e0538eab783d993f23639a08bc0ab68f9e80cad02cf789c78983ddd`
- `214-parity-partner-capacity/lean/WordParity214.lean`: `9319698b897581e02c161beb9f30110d08c93718993cd49aa02dd9bf148f2e68`
