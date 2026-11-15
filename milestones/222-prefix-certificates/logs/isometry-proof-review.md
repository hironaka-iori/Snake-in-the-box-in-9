# Compatible-partner pullback

Status: `PartnerIsometry222.pullback_partner` passed Lean on its first guarded compiler attempt in 1.098 seconds. Its axiom dependency report is empty. No repair or failed attempt occurred. This is standard symmetry invariance, with no novelty claim. The compiler is terminal and the slot was returned to the parent.

`PartnerIsometry222.pullback_partner` imports only `Std` and introduces no definitions. It assumes mutually inverse maps `f,g` and adjacency preservation by `f` in both directions. For a parent sequence `p` and an induced partner `q` of its image under `f`, it derives four conclusions for `g` composed with `q`: bounded injectivity, induced adjacency, the same designated joining parent index, and avoidance of every other bounded parent index.

The partner retains the same index range `0..m`, so its edge length is unchanged. The designated parent index is arbitrary in the generic theorem; choosing `root=0` or `root=n` preserves either parent endpoint. No classification of cube maps or parent isometry classes is assumed or proved.

Injectivity follows by applying `f` to an equality of pulled-back vertices and using the right inverse. Adjacency follows by applying the adjacency equivalence to the two pulled-back vertices and simplifying with the right inverse. The root equality uses the given joining equality and the left inverse. A forbidden pulled-back parent coincidence would map by `f` to a forbidden coincidence in the transformed partner. None of these conclusions is assumed as a premise.

Consequently, any proved exclusion of a given partner length for the original parent and the relevant joining endpoints also excludes that length for all images under such bijections. In the cube this applies to translations and coordinate permutations once their usual adjacency-preserving inverse maps are instantiated. Reversing the parent's indexing exchanges the two endpoints, already covered when both endpoints are excluded.

The theorem does not prove the numerical fixed-parent exclusion, enumerate the allowed cube vertices, or assemble a concrete map classification. Those remain separate exact-data/application obligations. It also does not extend an exclusion to different parent isometry classes or to constructions with a different face arrangement.

## Saved evidence

- Source: `lean/PartnerIsometry222.lean`, SHA256 `2481a8b9337eed4386296fddc34db94959bd4a0df1a077b8dd3be724e0aababb`.
- Receipt: `data/PartnerIsometry222-audit.json`, SHA256 `c4178878f94a61f5e4a17e1463d94439acf1cf3ba81a79a758c38b830fe50664`.
- Accepted object SHA256: `a9d404fc8da24575f9036b8fdf3825a94155f48672dbec5ecb52691625d2ac1e`.
- Compiler log: `logs/PartnerIsometry222-1794710420608529600/compiler.log`, SHA256 `859b176e19d12ef5568d88298d846744a8eb9e9e96099bd34af67552e6d34af4`.
- One Lean process ran with `-j1 -s8192`, a 60-second limit, a 256 MiB private-memory cap and a 768 MiB free-memory reserve. Startup free memory was 1,227,030,528 bytes. The recorded running sample had 1,217,343,488 free bytes and 34,783,232 compiler private bytes. These are sampled observations, not continuous peak measurements. All resource checks passed.
- The receipt pins source, execution plan, checker, native resource helper and the `Init` and `Std` objects. No software tests, solver runs or document edits were performed for this proof.
