# Final-audit scaling: can one machine check a theorem that imports ~200 GB of replay `.olean`?

Investigation of 15 November 2026 (branch `research/unconditional-241`). Lean 4.19.0
(`/home/user/lean-deps/toolchain/lean-4.19.0-linux`), on this machine (4 cores, 13.35 GiB limit,
cgroup v1). The experiments only read existing `.olean` files. Scratch modules were compiled with
`lean -o` into `/tmp/claude-0/`, and that directory was deleted afterwards. No audited module,
lake file, toolchain or existing `.olean` was changed.

## Answer

**RAM is not the wall. Disk and the kernel's limit on memory mappings are.**

- In Lean 4.19, `.olean` files are **mmapped read-only** at a fixed address (`src/library/module.cpp`).
  They are not read into the heap. A process that imports the whole 233 closure (34,278 files,
  23.0 GB mapped) has only **0.46 GB of anonymous memory**. The rest of its RSS is file-backed
  page cache.
- The 12.61 GB "peak RSS" of `UpperBound233` is almost all clean file-backed pages that the kernel
  could reclaim. `guarded_lake_build.py` counts them because it sums `ps rss`.
- Squeezing the default import does not crash it. It **thrashes**. The kernel's readahead (128 KB)
  and fault-around read large windows around pages that are touched in a scattered order, several
  times over (Lean makes several passes over all imported modules). Under a 1.5 to 6 GiB cgroup,
  the 233 audit re-read 60 to 229 GB of disk without finishing.
- With **one `madvise(MADV_RANDOM)` per `.olean` mapping** (an `LD_PRELOAD` hint of 20 lines, below;
  it changes no byte Lean reads), the full 233 audit (`import UpperBound233`, `#print axioms
  Snake9.upper_bound_233` → `[propext, Classical.choice, Quot.sound]`) **finished inside a 1 GiB
  memory cgroup in 310 s**, reading 25.3 GB. Under 2 GiB it took 233 s and read 18.7 GB. It was
  OOM-killed at 768 MiB, so the floor is between 0.77 and 1 GiB for 23 GB of `.olean`.
- **Extrapolation to 231** (a closure of about 220 GB and about 74,000 files): about 1-1.5 GB
  anonymous, plus a small hot page set. A 15 GB machine is enough for the RAM, with a margin of
  about ten times. The time is roughly one pass over the bytes: about 250 GB of 4 KB page faults,
  45-50 minutes at the 80-100 MB/s seen here.
- What a 15 GB / 27 GB cloud worker cannot do: (1) **hold the files**. 200 GB of new `.olean` plus
  the 23 GB 233 closure needs a disk of at least 250 GB. (2) **map them**. `vm.max_map_count` is
  65,530 here and on stock Linux. Each imported `.olean` is one mapping. The 233 audit already uses
  34,278. 20,000 new certificates at 2 modules each (Cnf and replay) bring this to about 74,000.
  **Lean 4.19 then segfaults**: this was measured with a mapping-hog shim (below). It does not fall
  back to `read`.

So **the cheapest sound path stays in Lean 4.19 and keeps the trust model unchanged**. Run the
final audit on **one** machine with:

- at least 250 GB of local disk (SSD) for ~200 GB of certificates;
- at least 8 GB of RAM (15-16 GB recommended);
- `vm.max_map_count` of at least 262,144 (one sysctl, root on that VM), or fewer files (below);
- the `MADV_RANDOM` preload, or readahead switched off for that disk (not tested here);
- a memory cap that counts anonymous memory only, or a cgroup, but not `ps rss`.

There is no theorem change, no new toolchain, no rebuild and no new axiom. A machine of the
cloud-worker class works if only its disk is enlarged and the sysctl is set.

The Lean module system (from v4.25/v4.30) would let the final process skip the certificate data
entirely. It costs a port of the whole project to a toolchain at least 11 versions newer and a
rebuild of every certificate. It is **not needed** for 231.

## Measurements

All runs used one `lean` process at `nice -n 10`, with `/proc/<pid>/status` and `/proc/<pid>/io`
sampled every 0.1 s and `wait4` rusage. "Limit" is a child memory cgroup
(`memory.limit_in_bytes`) created under this session's cgroup, so an OOM kill there could only hit
the test process. "Files / GB" is the number of distinct `.olean` files mapped by the process and
their total size. "Read" is `read_bytes` (real disk input). "Anon" and "File" are peak `RssAnon` and
`RssFile`.

`File` can exceed the limit because pages cached earlier by processes outside the cgroup are
charged to the parent cgroup.

| run | files / GB mapped | limit | wall | read | anon | file | result |
|---|---|---|---|---|---|---|---|
| no imports | 0 | — | 0.4 s | — | 0.028 | 0.21 | ok |
| 50 replay modules (0.12 GB certs) | 718 | — | 13.9 s cold, 0.5 s warm | — | 0.030-0.042 | 0.40 | ok |
| 200 replay modules (0.48 GB) | 1,415 | — | 38.5 s cold | — | 0.034 | 0.61 | ok |
| 800 replay modules (2.02 GB) | 4,354 / 2.79 | — | 112.7 s cold, 0.9 s warm | — | 0.055-0.059 | 1.43-1.46 | ok |
| 800 other replay modules (1.69 GB, cold) | 4,959 | 600 MiB | 107.8 s | — | 0.059 | 0.75 | **ok**: 1.25 M reclaim events, 59 k major faults |
| all 4,510 certificate modules of the 233 glue | 27,874 / 19.65 | 8 GiB | 215 s | 17.4 GB | 0.227 | 6.07 | ok |
| same | same | 4 GiB | 162 s | 35.7 GB | 0.228 | 3.77 | ok (re-reading) |
| same | same | 2 GiB | > 55 s | > 45 GB | 0.22 | 1.92 | thrash, stopped at 45 GB read |
| same + `MADV_RANDOM` | same | 2 GiB | **22.6 s** | **2.4 GB** | 0.227 | 2.10 | **ok** |
| same + `MADV_RANDOM` | same | 1 GiB | **35.5 s** | 3.9 GB | 0.224 | 1.12 | **ok** |
| **233 final audit** (`import UpperBound233` + `#print axioms`) | 34,278 / 23.05 | 3 GiB | 738 s | not recorded | 0.461 | 4.82 | ok, axioms clean (helped by pages charged to the parent) |
| same, repeated | same | 3 GiB | > 416 s | > 90 GB | 0.458 | 4.44 | thrash, stopped |
| same | same | 6 GiB | > 624 s | > 66.6 GB | 0.457 | 6.11 | thrash, stopped |
| same | same | 2 GiB | > 202 s | > 60 GB | 0.335 | 3.58 | thrash, stopped |
| same | same | 1.5 GiB | > 724 s | > 228.8 GB | 0.305 | 3.12 | thrash, stopped |
| `import UpperBound233` only (no `#print axioms`) | same | 3 GiB | > 111 s | > 60 GB | 0.337 | 3.18 | thrash, stopped: the import alone already thrashes |
| **233 final audit + `MADV_RANDOM`** | same | **2 GiB** | **233 s** | **18.7 GB** | 0.461 | 2.65 | **ok**, `[propext, Classical.choice, Quot.sound]` |
| **233 final audit + `MADV_RANDOM`** | same | **1 GiB** | **310 s** | **25.3 GB** | 0.461 | 1.61 | **ok**, same axioms |
| 233 final audit + `MADV_RANDOM` | same | 768 MiB | 210 s | 26.6 GB | 0.40 | — | OOM-killed in the test cgroup |
| 800 modules, 60,000 VMAs pre-consumed | 4,354 | — | 3.9 s | — | 0.061 | 1.48 | ok (the total stays under 65,530) |
| same, 61,500 / 62,500 / 63,000 VMAs pre-consumed | — | — | ~1 s | — | — | — | **SIGSEGV** (an import-free file runs fine with the same hog) |

**Derived numbers.**

- **RssAnon per GB of imported `.olean`: 0.012 GB/GB** for certificates only (0.227 GB for
  19.65 GB). It is 0.020 GB/GB for the full 233 audit with mathlib (0.46 GB for 23.05 GB). It
  depends on the file count more than on the bytes: about 7 KB per certificate file, and about
  0.23 GB for the 2,781 mathlib files and their extension state.
- **Hot file set with `MADV_RANDOM`: under 0.5 GB for the 233 closure.** The 1 GiB run finished
  with 0.46 GB anonymous memory, and the 768 MiB run did not.
- **Pages touched once.** The import alone touches about 12 % of the certificate bytes (2.4 GB for
  19.65 GB). `#print axioms` walks every proof body and brings the total to about 80 % (18.7 GB
  for 23 GB). That costs I/O, not resident memory.
- **Default behaviour.** Without the hint, about half of each mapped file becomes resident, through
  fault-around and readahead (1.43 GB of 2.79 GB for 800 modules). For a single 106 MB replay
  `.olean`, 45 % (47.8 MB) was resident after a bare import. A 4.5 MB data module was 98.6 %
  resident. That is the 12.61 GB of `UpperBound233` (about 0.55 × 23 GB). Below that size, the
  repeated passes re-read from disk.

**Composition of the 233 closure** (34,278 files):

| part | files | GB |
|---|---|---|
| replay `LocalWindowUnsat` (including the old split K modules in subdirectories) | 22,963 | 18.00 |
| `LocalWindowCnf` | 4,515 | 1.51 |
| mathlib + dependencies | 2,781 | 1.89 |
| Lean core (Init/Std/Lean) | 1,303 | 0.98 |
| other core, chain, floors overlay | 2,716 | 0.65 |

## What costs memory, and why (question 1)

From the 4.19 sources (`Lean/Environment.lean` in the toolchain, and `src/library/module.cpp` and
`src/runtime/compact.cpp` at tag `v4.19.0`):

- `importModulesCore` recurses over `mod.imports` for every module. It loads the **transitive
  closure** and cannot skip a module.
- `readModuleData` reads the header. It then calls `mmap(base_addr, size, PROT_READ, MAP_PRIVATE,
  fd, 0)` at an address derived from a hash of the module name: 64 KB aligned, below 0x7f0000000000.
- If the mapping lands at that address, `compacted_region::read` returns the root object with **no
  relocation pass**, so nothing is copied.
- If it lands elsewhere, the file is `malloc`ed, read and relocated. That costs anonymous memory
  equal to the file size. With 223 GB scattered over 127 TB of address space, collisions should
  cost well under 1 GB (an estimate). In the measurements no such cost appeared: anonymous memory
  stayed at 0.46 GB.
- `finalizeImport` then builds the constant and module hash maps (anonymous, per constant), the
  per-extension arrays of imported entries, and the extension states. Mathlib dominates this part.
- `#print axioms` walks every reachable constant body in the mapped regions.
- **Mapping limit.** Every file is one VMA, so the process needs one mapping per imported file
  plus about 1,000 others. Beyond `vm.max_map_count`, the experiment ends in SIGSEGV, not in the
  `malloc` fallback. The mechanism was not traced. One guess is a failed `mmap` for a thread
  stack or an allocation.

## Where the bytes of a replay `.olean` go (question 2)

- **Totals over the 4,510 certificates the 233 glue imports**: replay 10.47 GB and Cnf 1.38 GB.
  Cnf is 12 % of the pair.
- **Toy ctx-8 certificate** `C801234032A544643K15` (204,129 hints, 10,386 lemmas, W = 14): `.olean`
  613,392 B, of which 560,715 B (**91 %**) are the hex literal payloads.
  - Proof words: 204,129 hints (66 %), 67,926 lemma literals (22 %), and 2 × 10,386 length and
    terminator words.
  - Reference tables: 45.6 KB (8 % of the bytes).
  - Names, proof terms and headers: the remaining 9 %.
  - So it costs 3.0 B of `.olean` per hint here, against 2.66 B on average in 233.
- **Slack in the encoding**:
  - Order-0 entropy of the words is 11.9 bits per hint and 9.4 bits per literal, against 14 fixed.
    A perfect entropy coder would reach 1.92 B/hint (−32 %), but it needs a kernel-side decoder
    that costs kernel time.
  - Variable-length nibble or 7-bit codes are *larger*: 0.54-0.64 MB against 0.49 MB, because the
    values are spread evenly.
  - Milestone 26 found at most 8 % from denser hint words (§3c of its README).
  - Generic compression of the payload (xz −9) saves 26 %. So a compressed filesystem would not
    help much either.
  - There is nothing to deduplicate across certificates.
- **Keeping the data out of what importers load**: not possible in 4.19 (§3c below). Theorem
  values and all definitions, private ones included, are in the `.olean`, and the closure is loaded.

## Structural options (question 3)

**a. Chunked aggregation** (`allRefuted_of_merge`, chunk modules). It keeps each *elaboration* small:
the glue's `decide +kernel` merges. It does **not** reduce what the final process loads. The final
check imported only `UpperBound233` and still mapped all 34,278 files (measured). Keep it for the
glue's own cost, not for the audit.

**b. Lean module system.** The following was checked in the Lean sources fetched by tag from
GitHub. It was not run, because no new toolchain can be installed here.

- **v4.20-v4.24.** `module` / `isModule` and the `.olean`, `.olean.server` and `.olean.private`
  parts exist. Imports are still transitive.
- **From v4.25.0.** `importModulesCore` computes `needsData := needsData && (i.isExported ||
  importAll)`. A **non-`public` import of a non-root module is not loaded at all** ("none: do not
  import any `.olean*`").
- **In every module-system version** (`AddDecl.lean`): theorems, and definitions that are not
  exposed, are **exported as `axiomInfo`**. An importer's kernel sees only their statements.
- **Before v4.30.0**, `collectAxioms` walks bodies. A chunk theorem seen through the public
  interface would therefore be reported **as an axiom**, and `#print axioms` would not be clean.
- **From v4.30.0**, `exportedAxiomsExt` stores each exported declaration's axiom list when its
  module is compiled. Downstream `#print axioms` reads those lists "so axiom collection never
  crosses module boundaries".
- **Mathlib master** is written in `module` syntax and pins `v4.36.0-rc2`.

So with Lean 4.30 or later, the structure would be: chunk modules that *privately* import their
certificates and export `chunk_k : AllRefuted… chunk_k`, then a final `module` that imports the
chunks. The final process would load only the chunks' public `.olean`.

The result is a kernel-checked theorem *relative to the chunk statements*. Their proofs were checked
when the chunks compiled. The axiom report for them is metadata written by that compile. This is
the same trust in the `.olean` as today, since importing never re-checks, but the final process no
longer re-walks the proofs.

Cost of migrating:

- a toolchain jump of at least 11 versions and a matching mathlib (5 chain files import mathlib
  directly: `AggregateSingletonBound`, `CubeCoordinateAlgebra`, `EndpointGroups`,
  `FreshCoordinates`, `SquareIncidence`);
- re-elaboration of the core, chain and floors, with unknown breakage from 4.19 → 4.30+;
- a recompile of **every** certificate, because `.olean` files are tied to the toolchain. For 233
  alone that is 210 kernel-hours plus the older reused sets and the floors (2.3 CPU-hours);
- `module` / `public` headers in both generators.

That is weeks of porting and a full recertification for a saving that 4.19 already gets from
`MADV_RANDOM`. Not recommended now. It becomes interesting only if the audit must run on
small-disk machines.

**c. Private or auxiliary data in 4.19.** Two modules were compiled with the same 4 MB of
literals, one with the data in a `private def`, the other in a public `def`. Each exported a
theorem whose proof uses the data.

- `.olean` sizes: 4,497,504 B and 4,497,408 B.
- In an importer, the file is mapped and 98.6 % resident either way.
- `#print axioms` of the importer's theorem works, so the body is there.

`private` changes only the name (`_private…`), not what is stored or loaded. No saving.

**d. Using a theorem without its dependencies' `.olean` in 4.19: no.** `importModulesCore` always
loads the transitive closure. An `.olean` without its imports cannot be built honestly. The only
other ways are an axiom, or an `.olean` carrying an unchecked constant, and both change the trust
model. Several machines can check parts of the proof, as 233 did with 19 cloud-built certificates.
But the one process that states the final theorem must import everything.

**e. Fewer bytes and fewer hints.**

- In 233 the real LRAT hints were **54 % of `est_hints`** (2.93 G against 5.44 G over 3,108
  certificates; quartiles of hints/est 0.51, 0.58, 0.73). That came from the CaDiCaL portfolio in
  `cert233.py`: 1,355 with `--unsat --shrink=0`, 435 with `--chrono=0`, and others.
  - If the 231 plan's 70-90 G is an `est_hints` figure, expect **38-49 G hints, about 100-130 GB**.
    If it is already a real-hint figure, 190-240 GB stands.
- More core rounds and seeds (5 × 8, milestone 26 §5) took another **15-17 %** off hints, for
  15-43 s of solver time per window.
- A denser hint coding saves at most about 8 % with a cheap decoder.
- Together, about −20 to −25 % of bytes is realistic, and the kernel time falls in proportion.

**f. A large machine for the final audit only.** Without the hint, the measured working set is about
0.55 × the mapped GB (12.6 GB for 23 GB), so **about 125 GB of RAM** would be needed for a 225 GB
closure. With the hint:

| item | requirement |
|---|---|
| disk | closure + toolchain + mathlib: **new certificates + 25 GB**, SSD preferred. The 4 KB random-fault reads are the run time |
| RAM | 0.5 GB + 7 KB per certificate file + a few GB for `#print axioms` bookkeeping, so **4 GB would be enough and 15-16 GB leaves a wide margin**. Not measured beyond 23 GB; the guess is linear in files and constants |
| `vm.max_map_count` | at least the number of closure files + 2,000. Set **262,144** |
| time | about 1.1 × the closure size in disk reads plus about 1 CPU-minute per 10k files (233: 40 s user + 70-110 s system for 34k files): about 45-60 min for 225 GB at 80-100 MB/s. Faster on NVMe |
| memory guard | cap `RssAnon` (or use a cgroup), not `ps rss` |

## Recommendation (question 4)

For every target the trust model is unchanged, the toolchain stays 4.19, and the existing `.olean`
files are reused. The final audit is the usual `lean` process with the `MADV_RANDOM` preload (or
readahead disabled) and an anonymous-memory cap.

| new certificate `.olean` | closure (with the 233 closure) | files | what must be true |
|---|---|---|---|
| **~200 GB** (20,000 certificates) | ~225 GB | ~74,000 | an audit VM with **≥ 250 GB disk**, `vm.max_map_count` ≥ 100,000 (262,144), ≥ 8 GB RAM. Or keep ≤ 64,000 files by putting Cnf and replay in **one module per certificate** (20,000 new files, ~54,000 in all), still with the disk |
| **100 GB** | ~125 GB | 54-74 k | ≥ 150 GB disk, same sysctl or one module per certificate. RAM as above |
| **50 GB** | ~75 GB | ~45-74 k | ≥ 100 GB disk. This machine's volume would do if ~80 GB were freed. The `max_map_count` rule is unchanged: it depends on files, not bytes |
| **20 GB** | ~45 GB | ~40-74 k | ≥ 60 GB disk. Still **not** a 27 GB cloud worker, because the 233 closure alone is 23 GB. Same file-count rule |

The cheapest order of work:

1. Reduce the hints (portfolio + 5 × 8 cores), which also saves kernel-hours.
2. Generate one module per certificate, so that the closure stays under 65,530 mappings without
   root.
3. Change the build guard to cap `RssAnon`.
4. Run the final audit on one VM with enough disk.

Only if no VM with that disk can be had is the Lean 4.30+ module system the alternative. That
means a full port and a full recertification.

## What could not be verified here

- No toolchain newer than 4.19 was run. Every module-system claim comes from reading the tagged
  sources (`Environment.lean`, `AddDecl.lean`, `Util/CollectAxioms.lean`).
  - Not checked: whether a `module` final file can import non-`module` 4.19-style files. One code
    path rejects it ("cannot import non-`module` … from `module`").
  - Not checked: how `lean4checker`-style replay treats module builds.
  - Not checked: kernel speed under 4.30+.
- No run went beyond the 23 GB 233 closure. The 225 GB figures assume that anonymous memory and
  the hot set grow linearly with files and constants, and that the reads stay at one pass. The
  multi-pass structure of `finalizeImport` (per-extension sweeps) is the main risk to the second
  assumption.
- `read_ahead_kb` and fault-around were not changed: they are system-wide on this machine, which is
  shared with two other agents. The `MADV_RANDOM` preload was used instead. That readahead 0 gives
  the same effect is plausible but not tested.
- The SIGSEGV at the mapping limit was produced by pre-consuming VMAs in the same process. A real
  closure of more than 65,530 files was not built. The crash site was not traced.
- The first 3 GiB run of the 233 audit finished in 738 s, but some of its pages were charged to
  the parent cgroup, so it is not a clean 3 GiB result.
- Disk throughput on cloud workers or a larger VM was not measured.

## Appendix: the `MADV_RANDOM` preload

The preload is a performance hint only. It runs inside the `lean` process but changes neither the
mapped bytes nor any value Lean computes. Readahead disabled on the audit VM's disk would be an
alternative that injects no code.

```c
#define _GNU_SOURCE
#include <dlfcn.h>
#include <sys/mman.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
void *mmap(void *addr, size_t len, int prot, int flags, int fd, off_t off) {
  static void *(*real)(void *, size_t, int, int, int, off_t) = 0;
  if (!real) real = dlsym(RTLD_NEXT, "mmap");
  void *p = real(addr, len, prot, flags, fd, off);
  if (p != MAP_FAILED && fd >= 0) {
    char path[64], buf[4096];
    snprintf(path, sizeof path, "/proc/self/fd/%d", fd);
    ssize_t n = readlink(path, buf, sizeof buf - 1);
    if (n > 6) { buf[n] = 0; if (strcmp(buf + n - 6, ".olean") == 0) madvise(p, len, MADV_RANDOM); }
  }
  return p;
}
```

Build with `gcc -O2 -shared -fPIC -o madv.so madv.c -ldl` and run as
`LD_PRELOAD=$PWD/madv.so lean …`. The libraries of the 4.19 `lean` binary are dynamically linked,
and its `mmap` goes through libc, so the preload takes effect.

The mapping-limit test used a second preload. Its constructor maps N pages with `PROT_NONE` and
then sets every other page to `PROT_READ`. The pages cannot merge, so they use up N VMAs.
