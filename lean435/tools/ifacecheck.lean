/-
Interface-level kernel replay for the 4.35 assembly (milestone 36).

    IFACE=<interface dir> LEAN_PATH=<spec builds>:<glue build>:<interface dir>:<mathlib> \
      lean --run lean435/tools/ifacecheck.lean MODULE...

For each MODULE (a glue chunk, the top module Glue6SC<T>, or the final UpperBound<B>_435, built with all
three .olean parts), this re-runs the Lean kernel (`Environment.replay`) on every constant of the module
(public, server and private parts), on top of its imports loaded at the EXPORTED level. Each certificate
module under IFACE/LocalWindowCert and IFACE/LocalWindowCtxCert is given only its public `.olean` as
import artifact. It is leanchecker's `replayFromImports` (src/lean/LeanChecker.lean of the toolchain) with
the import level lowered, because stock leanchecker opens .olean.server/.olean.private of every import,
and certificates publish only their public .olean.

What it covers: a second pass of the SAME C++ kernel over the assembly (glue, top, final module),
against the certificates' public statements. What it does not cover: the certificates' own proofs (not
present in a public .olean), the spec layer (use stock leanchecker there), and kernel bugs (same kernel).
Run a few modules per process: the imported regions of each check are freed, but not all memory is.
-/
import Lean
open Lean

/-- Kernel replay of the constants of `module` (all three .olean parts), on top of its imports
loaded at the EXPORTED level only (interfaces), as leanchecker's `replayFromImports` does with full imports. -/
unsafe def check (arts : NameMap ImportArtifacts) (module : Name) : IO Nat := do
  let mFile ← findOLean module
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "no data" else
  let (mod, _) := parts[0]
  let last := parts[parts.size-1].1
  let (_, s) ← importModulesCore mod.imports (globalLevel := .exported) (arts := arts) |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (level := .exported) (isModule := true)
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  for name in last.constNames, ci in last.constants do
    newConstants := newConstants.insert name ci
  discard <| env.toKernelEnv.replay newConstants
  env.freeRegions
  return newConstants.size

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- certificate interfaces: only the public .olean exists; give exactly that file as the module's artifact
  let iface := (← IO.getEnv "IFACE").getD ""
  let mut arts : NameMap ImportArtifacts := {}
  for d in ["LocalWindowCert", "LocalWindowCtxCert"] do
    for e in (← System.FilePath.readDir (System.FilePath.mk iface / d)) do
      if e.path.extension == some "olean" then
        let stem := e.path.fileStem.getD ""
        arts := arts.insert (Name.mkStr (Name.mkSimple d) stem) (.ofArrays #[#[e.path], #[]])
  IO.println s!"{arts.size} interface-only modules"
  let mut bad := 0
  for a in args do
    try
      let n ← check arts a.toName
      IO.println s!"ok {a}: {n} constants replayed"
    catch e =>
      IO.eprintln s!"FAIL {a}: {e}"; bad := bad + 1
  return (if bad == 0 then 0 else 1)
