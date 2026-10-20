import Lean
import WinRup
/-!
# `rup_step`: emit one RUP step as a kernel-checked theorem, bypassing the elaborator

`rup_step k p n [h₁ h₂ …]` (inside `namespace M`, where `M.Inp : (Nat → Bool) → Prop` and
lemmas `M.d{hᵢ} : ∀ τ, Inp τ → msat τ M.c{hᵢ}` exist) adds
* `def M.c{k} : Mask := (p, n)` and
* `theorem M.d{k} : ∀ τ, Inp τ → msat τ M.c{k}` with proof
  `rup_sound (hs := [c{h₁}, …]) (of_decide_eq_true rfl) (as_cons … (d{h₁} τ h) …)`.

This code is untrusted: it only builds terms; every declaration goes through `addDecl`, i.e.
the Lean kernel, which evaluates `rup hs c` itself.  No `ofReduceBool` / native code is used.
-/
open Lean Elab Command

namespace WinRupCmd

syntax (name := rupStep) "rup_step " num num num "[" num* "]" : command

@[command_elab rupStep] def elabRupStep : CommandElab := fun stx => do
  let k := stx[1].isNatLit?.get!
  let p := stx[2].isNatLit?.get!
  let n := stx[3].isNatLit?.get!
  let hs := stx[5].getArgs.map fun s => s.isNatLit?.get!
  let ns ← getCurrNamespace
  let cN (i : Nat) := mkConst (ns ++ Name.mkSimple s!"c{i}")
  let dN (i : Nat) := mkConst (ns ++ Name.mkSimple s!"d{i}")
  let inp := mkConst (ns ++ `Inp)
  let nat := mkConst ``Nat
  let bool := mkConst ``Bool
  let maskT := mkConst ``WinRup.Mask
  let cK := ns ++ Name.mkSimple s!"c{k}"
  let maskVal := mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) nat nat (mkRawNatLit p) (mkRawNatLit n)
  liftCoreM <| addDecl <| .defnDecl
    { name := cK, levelParams := [], type := maskT, value := maskVal,
      hints := .abbrev, safety := .safe }
  -- hint list and its tails
  let mut tails : Array Expr := #[mkApp (mkConst ``List.nil [levelZero]) maskT]
  for i in hs.reverse do
    tails := tails.push (mkApp3 (mkConst ``List.cons [levelZero]) maskT (cN i) tails.back!)
  let hsE := tails.back!
  let tau := Expr.bvar 1
  let h := Expr.bvar 0
  let rupE := mkApp2 (mkConst ``WinRup.rup) hsE (mkConst cK)
  let tru := mkConst ``Bool.true
  let prop := mkApp3 (mkConst ``Eq [levelOne]) bool rupE tru
  let inst := mkApp2 (mkConst ``instDecidableEqBool) rupE tru
  let hr := mkApp3 (mkConst ``of_decide_eq_true) prop inst (mkApp2 (mkConst ``Eq.refl [levelOne]) bool tru)
  let mut acc := mkApp (mkConst ``WinRup.as_nil) tau
  let m := hs.size
  for j in [0:m] do
    let idx := m - 1 - j          -- position in hs
    let i := hs[idx]!
    let tl := tails[m - 1 - idx]!  -- list hs[idx+1:]
    acc := mkApp5 (mkConst ``WinRup.as_cons) tau (cN i) tl (mkApp2 (dN i) tau h) acc
  let body := mkApp5 (mkConst ``WinRup.rup_sound) tau hsE (mkConst cK) hr acc
  let fnT := mkForall `x .default nat bool
  let ty := mkForall `τ .default fnT (mkForall `h .default (mkApp inp (.bvar 0))
    (mkApp2 (mkConst ``WinRup.msat) (.bvar 1) (mkConst cK)))
  let val := mkLambda `τ .default fnT (mkLambda `h .default (mkApp inp (.bvar 0)) body)
  liftCoreM <| addDecl <| .thmDecl
    { name := ns ++ Name.mkSimple s!"d{k}", levelParams := [], type := ty, value := val }

end WinRupCmd
