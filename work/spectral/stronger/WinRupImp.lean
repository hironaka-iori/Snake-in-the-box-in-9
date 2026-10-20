import Lean
import WinRup
/-!
# `rup_imp_step`: RUP steps with a curried hint spine (smaller proof terms)

Same contract as `WinRupCmd.rup_step`, but the hint proofs are passed as plain arguments of
`rup_imp τ hs c hr : RupImp τ hs (msat τ c)`, where `RupImp τ [m₁, …, mₖ] P` is
`msat τ m₁ → … → msat τ mₖ → P`.  This avoids the `as_cons` chain with its explicit list
tails and roughly halves the size of the stored proof terms (and of the `.olean` files).
The command only builds terms and passes them to `addDecl`, so the kernel evaluates every
`rup hs c` itself; no `ofReduceBool` / native code is used.
-/
namespace WinRup

/-- `RupImp τ [m₁, …, mₖ] P = (msat τ m₁ → … → msat τ mₖ → P)` (direct `List.rec`). -/
def RupImp (τ : Nat → Bool) (l : List Mask) (P : Prop) : Prop :=
  List.rec (motive := fun _ => Prop) P (fun m _ ih => msat τ m → ih) l

theorem rupImp_intro (τ : Nat → Bool) (P : Prop) :
    ∀ hs : List Mask, (AllSat τ hs → P) → RupImp τ hs P
  | [], h => h trivial
  | _ :: ms, h => fun hm => rupImp_intro τ P ms (fun ha => h ⟨hm, ha⟩)

theorem rup_imp (τ : Nat → Bool) (hs : List Mask) (c : Mask) (hr : rup hs c = true) :
    RupImp τ hs (msat τ c) :=
  rupImp_intro τ _ hs (fun ha => rup_sound hr ha)

end WinRup

open Lean Elab Command

namespace WinRupImp

syntax (name := rupImpStep) "rup_imp_step " num num num "[" num* "]" : command

@[command_elab rupImpStep] def elabRupImpStep : CommandElab := fun stx => do
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
  let mut hsE : Expr := mkApp (mkConst ``List.nil [levelZero]) maskT
  for i in hs.reverse do
    hsE := mkApp3 (mkConst ``List.cons [levelZero]) maskT (cN i) hsE
  let tau := Expr.bvar 1
  let h := Expr.bvar 0
  let rupE := mkApp2 (mkConst ``WinRup.rup) hsE (mkConst cK)
  let tru := mkConst ``Bool.true
  let prop := mkApp3 (mkConst ``Eq [levelOne]) bool rupE tru
  let inst := mkApp2 (mkConst ``instDecidableEqBool) rupE tru
  let hr := mkApp3 (mkConst ``of_decide_eq_true) prop inst (mkApp2 (mkConst ``Eq.refl [levelOne]) bool tru)
  let mut body := mkApp4 (mkConst ``WinRup.rup_imp) tau hsE (mkConst cK) hr
  for i in hs do
    body := mkApp body (mkApp2 (dN i) tau h)
  let fnT := mkForall `x .default nat bool
  let ty := mkForall `τ .default fnT (mkForall `h .default (mkApp inp (.bvar 0))
    (mkApp2 (mkConst ``WinRup.msat) (.bvar 1) (mkConst cK)))
  let val := mkLambda `τ .default fnT (mkLambda `h .default (mkApp inp (.bvar 0)) body)
  liftCoreM <| addDecl <| .thmDecl
    { name := ns ++ Name.mkSimple s!"d{k}", levelParams := [], type := ty, value := val }

end WinRupImp
