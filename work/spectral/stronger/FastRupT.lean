import FastRupCmd
/-!
# FastRup targets: `F ⊨ C` for clauses derived anywhere in a shared proof

A shared (incremental) proof derives, besides ordinary lemmas, one *target* clause per window
(the negation of an unsat core of the window's assumption cube).  A target is an ordinary RUP
step whose mask is exported by its block; `fr_tgt` turns the export into
`∀ τ, Inp τ → clauseSat τ C` with `C` in the original variable numbering, through
`clauseSat_of_msatT`, the converse of `FastRup.msat_toMaskR` (the renamed mask `m` of `C` is
recomputed by the kernel, `M = m ||| tag` with a tag below `2^64`, i.e. in the padding bits).
The command only builds terms; the kernel checks them.
-/
namespace FastRup
open WinCNF

theorem litT_low {τ : Nat → Bool} {W x : Nat} (h : litT τ W x = true) : 64 ≤ x := by
  unfold litT at h
  by_cases h1 : x < 64
  · rw [if_pos h1] at h; exact absurd h Bool.false_ne_true
  · omega

theorem clauseSat_of_toMaskR {τ : Nat → Bool} {W T B : Nat} :
    ∀ {c : Clause} {vs : List Nat} {m : Nat}, toMaskR W T B c vs = some m →
      ∀ x, m.testBit x = true → litT (rtau τ T B) W x = true → clauseSat τ c
  | [], _, _, h, x, hx, _ => by
    simp only [toMaskR, Option.some.injEq] at h
    subst h; rw [Nat.zero_testBit] at hx; exact absurd hx Bool.false_ne_true
  | _ :: _, [], _, h, _, _, _ => by simp [toMaskR] at h
  | l :: c, v :: vs, m, h, x, hx, hl => by
    simp only [toMaskR] at h
    split at h
    · rename_i y m' hy hm'
      simp only [Option.some.injEq] at h
      subst h
      change (1 <<< y ||| m').testBit x = true at hx
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow] at hx
      rcases Bool.or_eq_true _ _ ▸ hx with hx | hx
      · have hxy : y = x := of_decide_eq_true hx
        subst hxy
        simp only [clauseSat, List.any_cons, Bool.or_eq_true]
        left
        cases l with
        | ofNat n =>
          simp only [litPosR] at hy
          split at hy
          · rename_i hc
            simp only [Option.some.injEq] at hy
            subst hy
            unfold litT at hl
            rw [if_neg (by omega), if_pos (by omega), show 64 + v - 64 = v by omega] at hl
            show τ n = true
            rw [← hc.2]; exact hl
          · exact absurd hy (by simp)
        | negSucc n =>
          simp only [litPosR] at hy
          split at hy
          · rename_i hc
            simp only [Option.some.injEq] at hy
            subst hy
            unfold litT at hl
            rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
              show 64 + W + v - 64 - W = v by omega] at hl
            show (!τ (n + 1)) = true
            rw [← hc.2]; exact hl
          · exact absurd hy (by simp)
      · have := clauseSat_of_toMaskR hm' x hx hl
        simp only [clauseSat, List.any_cons, Bool.or_eq_true] at this ⊢
        exact Or.inr this
    · exact absurd h (by simp)

theorem clauseSat_of_msatT (τ : Nat → Bool) (W T B : Nat) (c : Clause) (vs : List Nat)
    (m t M : Nat) (hm : toMaskR W T B c vs = some m) (he : Nat.beq M (Nat.lor m t) = true)
    (ht : Nat.blt t 18446744073709551616 = true) (hs : msat (rtau τ T B) W M) : clauseSat τ c := by
  obtain ⟨x, hx, hl⟩ := hs
  have hM := Nat.eq_of_beq_eq_true he
  have h64 := litT_low hl
  have ht' : t < 2 ^ 64 := by
    have := Nat.blt_eq.mp ht; simpa using this
  have htx : t.testBit x = false := Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le ht' (Nat.pow_le_pow_right (by decide) h64))
  rw [hM] at hx
  change (m ||| t).testBit x = true at hx
  rw [Nat.testBit_or, htx, Bool.or_false] at hx
  exact clauseSat_of_toMaskR hm x hx hl

end FastRup

open Lean Elab Command

namespace FastRupCmd

syntax (name := frTgt) "fr_tgt " ident ident num num num num num* : command

/-- `fr_tgt NAME BLOCK k W B Wo  p… 0 v… 0 t` : theorem `NAME : ∀ τ, Inp τ → clauseSat τ C` where
`C` has the literal positions `p…` (original numbering, stride `Wo`), `v…` are the renamed
variables of its literals, `k` the export slot of `BLOCK` that holds its mask, `t` its tag. -/
@[command_elab frTgt] def elabFrTgt : CommandElab := fun stx => do
  let name := stx[1].getId
  let bname := stx[2].getId
  let k := stx[3].isNatLit?.get!
  let W := stx[4].isNatLit?.get!
  let B := stx[5].isNatLit?.get!
  let Wo := stx[6].isNatLit?.get!
  let xs : Array Nat := stx[7].getArgs.map fun s => s.isNatLit?.get!
  let ns ← getCurrNamespace
  let env ← getEnv
  let mut i := 0
  let mut ps : Array Nat := #[]
  while xs[i]! != 0 do ps := ps.push xs[i]!; i := i + 1
  i := i + 1
  let mut vs : Array Nat := #[]
  while xs[i]! != 0 do vs := vs.push xs[i]!; i := i + 1
  let tg := xs[i + 1]!
  let bn := ns ++ bname
  let some ci := env.find? bn | throwError "missing {bn}"
  let ms := exportMasks ci.type
  let n := ms.size
  let natE := mkConst ``Nat
  let WE := mkRawNatLit W
  let BE := mkRawNatLit B
  let RT := mkConst (ns ++ `RT)
  let inp := mkConst (ns ++ `Inp)
  let cl := listE intE (ps.map (litE Wo))
  let vsE := listE natE (vs.map mkRawNatLit)
  let m := Id.run do
    let mut acc := 0
    for (p, v) in ps.zip vs do
      acc := acc ||| (1 <<< (64 + (if p < Wo then v else W + v)))
    return acc
  let M := ms[k]!
  let fnT := mkForall `x .default natE (mkConst ``Bool)
  let tauAt (j : Nat) : Expr := mkApp3 (mkConst ``FastRup.rtau) (.bvar j) RT BE
  let optNat := mkApp (mkConst ``Option [levelZero]) natE
  let reflB := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true)
  -- body under binders τ h e₀ … e_{n-1}: τ = bvar (n+1)
  let goal (j : Nat) : Expr := mkApp2 (mkConst ``WinCNF.clauseSat) (.bvar j) cl
  let body := mkAppN (mkConst ``FastRup.clauseSat_of_msatT)
    #[.bvar (n + 1), WE, RT, BE, cl, vsE, mkRawNatLit m, mkRawNatLit tg, M,
      mkApp2 (mkConst ``Eq.refl [levelOne]) optNat (mkApp2 (mkConst ``Option.some [levelZero]) natE (mkRawNatLit m)),
      reflB, reflB, .bvar (n - 1 - k)]
  let mut lam := body
  for i' in [0:n] do
    let j := n - 1 - i'
    lam := mkLambda (Name.mkSimple s!"e{j}") .default (mkApp3 (mkConst ``FastRup.msat) (tauAt (j + 1)) WE ms[j]!) lam
  let val0 := mkAppN (mkConst bn) #[.bvar 1, .bvar 0, goal 1, lam]
  let ty := mkForall `τ .default fnT (mkForall `h .default (mkApp inp (.bvar 0)) (goal 1))
  let val := mkLambda `τ .default fnT (mkLambda `h .default (mkApp inp (.bvar 0)) val0)
  liftCoreM <| addDecl <| .thmDecl { name := ns ++ name, levelParams := [], type := ty, value := val }

end FastRupCmd
