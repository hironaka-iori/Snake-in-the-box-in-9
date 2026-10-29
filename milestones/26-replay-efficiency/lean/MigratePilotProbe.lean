import MigratePilotAgg
import Lean

/-! Which replay modules are loaded, and the exact statement of each `unsat` and of the pilot
theorems (printed in full, with a structural hash). -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames.filter fun n =>
    (`LocalWindowUnsat).isPrefixOf n || n == `ProofPack || n == `NatPack
  logInfo m!"replay modules loaded ({mods.size}): {mods.toList}"
  for c in [``Snake9.LocalWindow.Q012304A26432.unsat, ``Snake9.LocalWindow.Q01234A4244.unsat,
            ``Snake9.LocalWindow.R012301A34324.unsat, ``Snake9.LocalWindow.Q012304A26432.cnf,
            ``Snake9.LocalWindow.pilotUnsat, ``Snake9.LocalWindow.pilotRefuted] do
    let some ci := env.find? c | throwError m!"missing {c}"
    let some idx := env.getModuleIdxFor? c | throwError m!"no module for {c}"
    logInfo m!"{c} [{env.header.moduleNames[idx.toNat]!}] : {ci.type} (hash {ci.type.hash})"
