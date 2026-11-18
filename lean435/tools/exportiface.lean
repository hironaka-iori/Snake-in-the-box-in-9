/-
Export for independent kernels (milestone 36).

    IFACE=<interface dir> LEAN_PATH=... lean --run lean435/tools/exportiface.lean MODULE [CONSTANT...] > out

Writes, in lean4export format (toolchain library LeanExport), the closure of the given constants of
MODULE (default: every constant of MODULE). The environment is built as in ifacecheck.lean: MODULE's own
constants (all three .olean parts) are replayed by the kernel on top of its imports at the EXPORTED
level, each certificate given only its public .olean. Imported constants whose bodies are not exported
(theorems, non-exposed definitions) appear in the export as axioms: they are the assumptions of the
check. The output starts after the compiler's deprecation warning lines (keep from the {"meta" line).
Checkers: nanoda_bin (Rust, independent) and leanchecker --from-export (Lean's C++ kernel); see
xkernel435.sh.
-/
import Lean
import LeanExport.Basic
open Lean

/-- Export (lean4export format) the closure of constants CS of module ROOT: ROOT's own constants (all
three .olean parts) replayed by the kernel on top of its imports at the EXPORTED level, certificates
given only their public .olean (IFACE). Usage: lean --run ExportIface.lean ROOT CS... > file -/
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let iface := (← IO.getEnv "IFACE").getD ""
  let mut arts : NameMap ImportArtifacts := {}
  for d in ["LocalWindowCert", "LocalWindowCtxCert"] do
    for e in (← System.FilePath.readDir (System.FilePath.mk iface / d)) do
      if e.path.extension == some "olean" then
        arts := arts.insert (Name.mkStr (Name.mkSimple d) (e.path.fileStem.getD "")) (.ofArrays #[#[e.path], #[]])
  let module := args.head!.toName
  let mFile ← findOLean module
  let fnames := #[mFile, OLeanLevel.server.adjustFileName mFile, OLeanLevel.private.adjustFileName mFile]
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "no data" else
  let (mod, _) := parts[0]
  let last := parts[parts.size-1].1
  let (_, s) ← importModulesCore mod.imports (globalLevel := .exported) (arts := arts) |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (level := .exported) (isModule := true)
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  for name in last.constNames, ci in last.constants do
    newConstants := newConstants.insert name ci
  let env ← env.toKernelEnv.replay newConstants
  let env := Environment.ofKernelEnv env
  -- default: every constant of the module itself (all parts), with its closure
  let cs := if args.tail.isEmpty then last.constNames.toList else args.tail.map (·.toName)
  LeanExport.dumpEnv env (some cs) []
