# Round 232 final document review

**No outstanding blocking issue found.** The final additions correctly state the minority-class criterion, the combined omission result and its isometry transport, and the exact restricted maximum of 191. Native exclusions remain distinguished from the seven new checked implications. The maintained global interval remains 191 <= a(9) <= 233.

## Reviewed scope

Read the main manuscript's updated abstract, reading guide, complete `sec:minority232` proposition and proof, finite-result paragraph, combined conclusion, restricted-maximum paragraph, proposed next step, verification additions, and new bibliography entry. Also checked the adjoining majority-class conclusion for consistency. Read the short paper's complete minority section, revised majority transition, remaining questions, and bibliography entry, and all 37 lines of `MATHEMATICAL_NOTE.md`. Reviewed the two new Lean sources and their saved compiler/audit evidence. This is a bounded review of these additions and their dependencies, not a new complete review of the 12,301-line manuscript.

## Mathematical and evidence assessment

- The proposition requires at least two fixed vertices. Its Hamiltonian endpoints are therefore distinct. Their singleton-neighbour labels cannot coincide, and cannot coincide with a two-neighbour internal label. Exact selected-neighbour sets and same-parity nonadjacency justify the induced lift. The converse correctly removes the two opposite-colour endpoints. The resulting length is 2|U|.
- The finite counts match the independently verified evidence: 145 fixed classes, two insufficient-port cases, 62 unsupported-leaf cases, and 81 native circuit exclusions. Of those 81, 33 have positive augmented-cycle separators; 48 retain native circuit evidence alone. The separator inequality uses the cycle bound of |S| remaining components, with nonempty S, rather than the path bound |S|+1.
- The combined 192-edge conclusion is valid. An entirely retained saved 96-set would either equal the candidate's minority class or be contained in its 97-vertex majority class. The two finite covers exclude those alternatives. Thus at least one saved vertex of each parity is omitted relative to every saved seed.
- Inverse-isometry transport is justified: an inverse cube automorphism preserves inducedness, containment, length, and parity classes up to exchange. This extends the restricted conclusion to isometric copies of saved seeds without claiming an enumeration of isometries or a complete classification of seeds. Its native-evidence qualification is retained.
- The exact restricted maximum of 191 requires one complete selected parity class to equal a saved 96-set. Alternation bounds the other selected class by 97 and the total edge length by 192. The native exclusion removes that last length, and the original seed attains 191. The argument establishes the maximum within the stated exact-class family; it does not assert a global maximum or extend the same counting argument to mere containment of the 96-set.
- The next-step discussion is prospective. Starting from 95 retained vertices, adding one new same-parity vertex changes neighbour counts only at its nine opposite-parity neighbours. The text does not claim the resulting exchange family has already been exhausted.
- Contributor status remains appropriately qualified. The maintained bound is 233 with its independent-rebuild caveat. The note records that the inspected update through `61e6655e` changes scheduling and supplies no newly inspected unconditional 231 assembly.

## Checked-source claims

`MinorityContraction232.lean` contains the four described results: singleton/internal label distinction, two-endpoint attachment, the minority constructor, and endpoint singleton adjacency extracted from an actual even-length indexed path. Its constructor retains explicit distinctness, disjointness and adjacency premises; concrete cube classes, literal graph extraction, and native contradictions are not silently discharged by it.

`FixedColour232.lean` contains three count implications. `length_le_twice_colour` assumes an alternating natural-valued indicator sequence and the exact colour sum. `strict_length_bound` additionally assumes exclusion of the top length. `fixed_96_bound` specializes this to a colour count of 96 and an explicit length-192 exclusion, yielding length at most 191. The paper accurately leaves actual cube-to-count extraction, the native exclusion, and the attaining seed as separate evidence.

Both saved audit receipts report `PASS`, exit code zero, and no resource stop. The four plus three axiom reports use only the standard recorded axioms. Their current source, object, and compiler-log hashes agree with the receipts. No compiler was invoked by this reviewer, and the full inherited dependency closure was not independently rebuilt.

| Saved evidence | SHA-256 |
|---|---|
| `data/MinorityContraction232-audit.json` | `b7f243e098a88c9dfaea4966ef01ccc2aa1b42e936bb9f098fa3e7d18c4905ee` |
| `lean/MinorityContraction232.lean` | `ceab873aad1f605159e0cfc58062797e0636918f70721ea4960a1fb32d3fd76d` |
| `data/FixedColour232-audit.json` | `c593495559b72620cbf07b6088b3bd91c2cb6ca818cf3f9bf2aa627ce1057c11` |
| `lean/FixedColour232.lean` | `eb6b5aac45b3cee0261a9486419407deea71f2901c6d1e82f413842b692e214f` |

These paths are relative to `milestones/232-minority-contraction`.

## Correction verified

The initial short-paper wording “keeping any complete saved 96-vertex colour class unchanged” could be read as mere containment. The final wording explicitly requires one complete selected colour class to equal a saved 96-set. This matches the exact-count argument and the already precise main manuscript and note. The correction was reread in both final copies. No further revision is requested by this review.

## Preserved settings and final hashes

The complete author commands and complete `hypersetup` command were compared with the round-232 pre-edit snapshots and are unchanged. Both manuscripts retain Iori Hironaka, Tommy Ma, and Steven Zhan in their existing order and formatting. The main PDF settings, including its author metadata, are unchanged; the short paper continues to have no separate `hypersetup` command. Each authoritative original is byte-identical to its corresponding `E:/Snake-in-a-box/paper/` mirror.

| Final file | Bytes | SHA-256 |
|---|---:|---|
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex` | 770132 | `aef0b484b265c163b7eebd54c2c994d610ce252c489429b06bdf51c2fbeab4d8` |
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex` | 38380 | `cc144fe6e6a24036b490c6b827e570c12366fb15c3a04c0d6f70953c9bfece98` |
| `E:/Snake-in-a-box/milestones/232-minority-contraction/MATHEMATICAL_NOTE.md` | 4834 | `540f7d4e40612cf618c0229bcc267d9dab8f0f8462c5066e18098d42b7c51c84` |

The main and short sources contain 12,301 and 721 lines, respectively. No solver, compiler, software test, manuscript edit, or modification of existing evidence was performed. LaTeX compilation and rendered-page inspection are separate from this source review. Only this report was written.
