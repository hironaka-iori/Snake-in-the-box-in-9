import Lean
import Std.Data.HashMap
import FastRup
/-!
# Commands that turn LRAT data into kernel-checked `FastRup` proofs

The commands only *build terms* and submit them with `addDecl`; the kernel type-checks every
declaration and evaluates every closing `finF … = true` itself.  Nothing here is trusted: wrong
data makes `addDecl` fail.  No `ofReduceBool`, `native_decide` or native code is involved.

* `fr_cnf W CH idx pos… 0 …` defines the chunks `G0, G1, …` (`CH` clauses each) of the used input
  clauses as `WinCNF.CNF` values (positions in original numbering: `v`, or `W + v` for `-v`).
  The module then states `F` (a balanced `++` of the chunks), `Inp τ := ∀ c ∈ F, clauseSat τ c`
  and the renaming table `RT` in plain source.
* `fr_chunk k W B v'…` proves `I{k} : ∀ τ, Inp τ → ∀ Q, (msat (rtau τ RT B) W m₁ → … → Q) → Q`
  for the clauses of `G{k}` (renamed variables `v'` per literal, re-checked against `RT`).
* `fr_block Name W B data` proves `Name : ∀ τ, Inp τ → ∀ Q, (msat … e₁ → … → msat … eₙ → Q) → Q`
  (the exported clauses), with one `let` per RUP step; earlier chunks and blocks are used by
  applying their theorems to a continuation that binds their exports.
-/
open Lean Elab Command

namespace FastRupCmd

def natE : Expr := mkConst ``Nat
def intE : Expr := mkConst ``Int
def clauseTy : Expr := mkApp (mkConst ``List [levelZero]) intE

def litE (W x : Nat) : Expr :=
  if x < W then mkApp (mkConst ``Int.ofNat) (mkRawNatLit x)
  else mkApp (mkConst ``Int.negSucc) (mkRawNatLit (x - W - 1))

def listE (ty : Expr) (xs : Array Expr) : Expr := Id.run do
  let mut e := mkApp (mkConst ``List.nil [levelZero]) ty
  for x in xs.reverse do
    e := mkApp3 (mkConst ``List.cons [levelZero]) ty x e
  return e

/-- per-clause tag for the 64 padding bits (`0` for the empty clause) -/
def tag (id : Nat) (empty : Bool) : Nat :=
  if empty then 0 else (id * 11400714819323198485 + 7146381651874099225) % 2 ^ 64

/-- mask of a clause with literal positions `ps` (data positions are shifted by 64) -/
def maskOf (id : Nat) (ps : Array Nat) : Nat :=
  ps.foldl (fun m x => m ||| (1 <<< (64 + x))) (tag id ps.isEmpty)

/-- split `0`-terminated records -/
def records (xs : Array Nat) (start : Nat) : Array (Array Nat) := Id.run do
  let mut out := #[]
  let mut cur := #[]
  for i in [start:xs.size] do
    let x := xs[i]!
    if x == 0 then out := out.push cur; cur := #[] else cur := cur.push x
  return out

def nums (stx : Syntax) : Array Nat := stx.getArgs.map fun s => s.isNatLit?.get!

syntax (name := frCnf) "fr_cnf " num num num* : command
@[command_elab frCnf] def elabFrCnf : CommandElab := fun stx => do
  let W := stx[1].isNatLit?.get!
  let ch := stx[2].isNatLit?.get!
  let recs := records (nums stx[3]) 0
  let ns ← getCurrNamespace
  let mut k := 0
  let mut i := 0
  while i < recs.size do
    let grp := recs.extract i (i + ch)
    let cls := grp.map fun r => listE intE ((r.extract 1 r.size).map (litE W))
    liftCoreM <| addDecl <| .defnDecl
      { name := ns ++ Name.mkSimple s!"G{k}", levelParams := [], type := mkConst ``WinCNF.CNF,
        value := listE clauseTy cls, hints := .abbrev, safety := .safe }
    k := k + 1
    i := i + ch

syntax (name := frChunk) "fr_chunk " num num num num* : command
syntax (name := frBlock) "fr_block " ident num num num* : command

/-- export masks of a provider `∀ τ h Q, (msat _ W c₁ → … → msat _ W cₑ → Q) → Q` -/
def exportMasks (ty : Expr) : Array Expr := Id.run do
  let mut t := ty.bindingBody!.bindingBody!.bindingBody!.bindingDomain!
  let mut out := #[]
  while t.isForall do
    out := out.push t.bindingDomain!.appArg!
    t := t.bindingBody!
  return out

/-- `∀ Q, (msat (rtau τ RT B) W m₁ → … → Q) → Q` under binders `τ h` (τ = bvar 1) -/
def cpsType (tauAt : Nat → Expr) (WE : Expr) (ms : Array Expr) : Expr := Id.run do
  let msatC := mkConst ``FastRup.msat
  let mut tel := Expr.bvar ms.size
  for i' in [0:ms.size] do
    let i := ms.size - 1 - i'
    tel := mkForall `e .default (mkApp3 msatC (tauAt (i + 2)) WE ms[i]!) tel
  return mkForall `Q .default (mkSort levelZero) (mkForall `k .default tel (.bvar 1))

/-- the `∈`-path to constant `g` inside `F = … ++ …` (balanced): list of (left?, as, bs) from the root -/
def findPath : Nat → Expr → Name → Option (List (Bool × Expr × Expr))
  | 0, _, _ => none
  | fuel + 1, e, g =>
    if e.isConstOf g then some []
    else if e.isAppOfArity ``HAppend.hAppend 6 then
      let a := e.appFn!.appArg!
      let b := e.appArg!
      match findPath fuel a g with
      | some p => some ((true, a, b) :: p)
      | none => match findPath fuel b g with
        | some p => some ((false, a, b) :: p)
        | none => none
    else none

/-- `fr_chunk k W B  v'…` : theorem `I{k}` exporting the clauses of chunk `G{k}` (renamed variables
`v'` per literal, in order), as a CPS statement. -/
@[command_elab frChunk] def elabFrChunk : CommandElab := fun stx => do
  let k := stx[1].isNatLit?.get!
  let W := stx[2].isNatLit?.get!
  let B := stx[3].isNatLit?.get!
  let vsAll : Array Nat := stx[4].getArgs.map fun s => s.isNatLit?.get!
  let ns ← getCurrNamespace
  let env ← getEnv
  let WE := mkRawNatLit W
  let BE := mkRawNatLit B
  let RT := mkConst (ns ++ `RT)
  let inp := mkConst (ns ++ `Inp)
  let gName := ns ++ Name.mkSimple s!"G{k}"
  let some (.defnInfo fi) := env.find? (ns ++ `F) | throwError "no F"
  let some (.defnInfo gi) := env.find? gName | throwError "no {gName}"
  let some path := findPath 64 fi.value gName | throwError "G{k} not in F"
  let tauAt (i : Nat) : Expr := mkApp3 (mkConst ``FastRup.rtau) (.bvar i) RT BE
  let natE := mkConst ``Nat
  let optNat := mkApp (mkConst ``Option [levelZero]) natE
  let consN := mkApp (mkConst ``List.cons [levelZero]) natE
  let nilN := mkApp (mkConst ``List.nil [levelZero]) natE
  -- elements / tails of the chunk
  let mut elems : Array Expr := #[]
  let mut tails : Array Expr := #[]
  let mut l := gi.value
  while l.isAppOfArity ``List.cons 3 do
    elems := elems.push l.appFn!.appArg!
    tails := tails.push l.appArg!
    l := l.appArg!
  let mut masks : Array Expr := #[]
  let mut links : Array Expr := #[]
  let mut p := 0
  for j in [0:elems.size] do
    let cl := elems[j]!
    -- literals of the clause (Int.ofNat n / Int.negSucc n) and their renamed variables
    let mut lits : Array Nat := #[]   -- data positions: v (pos) / W + v (neg) in *renamed* numbering
    let mut vsE := nilN
    let mut vsArr : Array Nat := #[]
    let mut e := cl
    while e.isAppOfArity ``List.cons 3 do
      let lit := e.appFn!.appArg!
      let v' := vsAll[p]!
      p := p + 1
      vsArr := vsArr.push v'
      if lit.isAppOfArity ``Int.ofNat 1 then lits := lits.push v' else lits := lits.push (W + v')
      e := e.appArg!
    for v' in vsArr.reverse do vsE := mkApp2 consN (mkRawNatLit v') vsE
    let m := lits.foldl (fun acc x => acc ||| (1 <<< (64 + x))) 0
    let tg := tag (k * 100000 + j) false
    let mE := mkRawNatLit m
    let mT := mkRawNatLit (m ||| tg)
    masks := masks.push mT
    -- membership cl ∈ F
    let mut mem := mkApp3 (mkConst ``List.mem_cons_self [levelZero]) clauseTy cl tails[j]!
    for jj' in [0:j] do
      let jj := j - 1 - jj'
      mem := mkApp5 (mkConst ``List.mem_cons_of_mem [levelZero]) clauseTy elems[jj]! cl tails[jj]! mem
    for (isL, a, b) in path.reverse do
      mem := if isL then mkApp5 (mkConst ``List.mem_append_left [levelZero]) clauseTy cl a b mem
             else mkApp5 (mkConst ``List.mem_append_right [levelZero]) clauseTy cl a b mem
    -- link at depth: fun τ h Q k => k link…   (τ = bvar 3, h = bvar 2)
    let someM := mkApp2 (mkConst ``Option.some [levelZero]) natE mE
    let refl := mkApp2 (mkConst ``Eq.refl [levelOne]) optNat someM
    let base := mkAppN (mkConst ``FastRup.msat_toMaskR) #[.bvar 3, WE, RT, BE, cl, vsE, mE, refl, mkApp2 (.bvar 2) cl mem]
    links := links.push (mkAppN (mkConst ``FastRup.msat_lor) #[tauAt 3, WE, mE, mkRawNatLit tg, base])
  let mut body : Expr := .bvar 0
  for x in links do body := mkApp body x
  let K := cpsType tauAt WE masks
  let fnT := mkForall `x .default natE (mkConst ``Bool)
  let ty := mkForall `τ .default fnT (mkForall `h .default (mkApp inp (.bvar 0)) K)
  let telV := (K.bindingBody!).bindingDomain!
  let val := mkLambda `τ .default fnT (mkLambda `h .default (mkApp inp (.bvar 0))
    (mkLambda `Q .default (mkSort levelZero) (mkLambda `k .default telV body)))
  liftCoreM <| addDecl <| .thmDecl { name := ns ++ Name.mkSimple s!"I{k}", levelParams := [], type := ty, value := val }

/-- Block command.  Data: `nE slot…  nP prov…  steps`; a provider is `2k+1` (chunk `I{k}`) or
`2b` (block `B{b}`); a step is `id pos… 0 (slot+1)… 0` (positions in renamed numbering).
Slots: the exports of the providers in the order given, then one per step. -/
@[command_elab frBlock] def elabFrBlock : CommandElab := fun stx => do
  let name := stx[1].getId
  let W := stx[2].isNatLit?.get!
  let B := stx[3].isNatLit?.get!
  let xs : Array Nat := stx[4].getArgs.map fun s => s.isNatLit?.get!
  let ns ← getCurrNamespace
  let env ← getEnv
  let WE := mkRawNatLit W
  let BE := mkRawNatLit B
  let RT := mkConst (ns ++ `RT)
  let tauAt (i : Nat) : Expr := mkApp3 (mkConst ``FastRup.rtau) (.bvar i) RT BE
  let inp := mkConst (ns ++ `Inp)
  let msatC := mkConst ``FastRup.msat
  let natE := mkConst ``Nat
  let propE := mkSort levelZero
  let fnT := mkForall `x .default natE (mkConst ``Bool)
  let stepW := mkApp (mkConst ``FastRup.stepF) WE
  let padE := mkConst ``FastRup.pad
  let refl := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true)
  let nE := xs[0]!
  let expSlots := xs.extract 1 (1 + nE)
  let mut p := 1 + nE
  let nP := xs[p]!
  let provs := xs.extract (p + 1) (p + 1 + nP)
  p := p + 1 + nP
  let mut masks : Array Expr := #[]
  let mut provMasks : Array (Name × Array Expr) := #[]
  for q in provs do
    let pn := ns ++ Name.mkSimple (if q % 2 == 1 then s!"I{q / 2}" else s!"B{q / 2}")
    let some ci := env.find? pn | throwError "missing {pn}"
    let ms := exportMasks ci.type
    provMasks := provMasks.push (pn, ms)
    masks := masks ++ ms
  -- step lets at depth D = slot index: τ = bvar (D+3), h = bvar (D+2), Q = bvar (D+1), k = bvar D
  let mut lets : Array (Name × Expr × Expr) := #[]
  let mut cur : Array Nat := #[]
  let mut inHints := false
  let mut hs : Array Nat := #[]
  let mut stepId := 0
  let mut mE : Expr := natE
  for k in [p:xs.size] do
    let x := xs[k]!
    if !inHints then
      if x == 0 then
        stepId := cur[0]!
        mE := mkRawNatLit (maskOf stepId (cur.extract 1 cur.size))
        inHints := true; hs := #[]
      else cur := cur.push x
    else if x != 0 then hs := hs.push (x - 1)
    else
      let D := masks.size
      let tau := tauAt (D + 4)       -- inside `fun hn`
      let st := mkApp2 (mkConst ``FastRup.step_sound) tau WE
      let mut F := mkApp2 (mkConst ``Nat.lor) mE padE
      let mut pf := mkAppN (mkConst ``FastRup.start) #[tau, WE, mE, .bvar 0]
      for i in [0:hs.size - 1] do
        let s := hs[i]!
        let hm := masks[s]!
        pf := mkApp4 st F hm (.bvar (D - s)) pf
        F := mkApp2 stepW F hm
      let sl := hs[hs.size - 1]!
      let body := mkAppN (mkConst ``FastRup.close) #[tau, WE, F, masks[sl]!, .bvar (D - sl), pf, refl]
      let tauO := tauAt (D + 3)
      let lam := mkLambda `hn .default (mkApp (mkConst ``Not) (mkApp3 msatC tauO WE mE)) body
      lets := lets.push (Name.mkSimple s!"x{stepId}", mkApp3 msatC tauO WE mE,
        mkAppN (mkConst ``FastRup.rup) #[tauO, WE, mE, lam])
      masks := masks.push mE
      inHints := false; cur := #[]
  let N := masks.size
  let mut body := Expr.bvar N
  for s in expSlots do body := mkApp body (.bvar (N - 1 - s))
  for i' in [0:lets.size] do
    let i := lets.size - 1 - i'
    let (n, t, v) := lets[i]!
    body := mkLet n t v body
  let mut off := N - lets.size
  for c' in [0:provMasks.size] do
    let c := provMasks.size - 1 - c'
    let (pn, ms) := provMasks[c]!
    off := off - ms.size
    let mut lam := body
    for i' in [0:ms.size] do
      let i := ms.size - 1 - i'
      let D := off + i
      lam := mkLambda (Name.mkSimple s!"e{D}") .default (mkApp3 msatC (tauAt (D + 3)) WE ms[i]!) lam
    let D := off
    body := mkAppN (mkConst pn) #[.bvar (D + 3), .bvar (D + 2), .bvar (D + 1), lam]
  let expM := expSlots.map fun s => masks[s]!
  let K := cpsType tauAt WE expM
  let ty := mkForall `τ .default fnT (mkForall `h .default (mkApp inp (.bvar 0)) K)
  let telV := (K.bindingBody!).bindingDomain!
  let val := mkLambda `τ .default fnT (mkLambda `h .default (mkApp inp (.bvar 0))
    (mkLambda `Q .default propE (mkLambda `k .default telV body)))
  liftCoreM <| addDecl <| .thmDecl { name := ns ++ name, levelParams := [], type := ty, value := val }

end FastRupCmd
