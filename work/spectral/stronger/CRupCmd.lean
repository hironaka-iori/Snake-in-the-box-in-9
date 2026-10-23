import FastRupT
import CRup
/-!
# Commands that turn LRAT data into kernel-checked `CRup` proofs

As in `FastRupCmd`, the commands only build terms and submit them with `addDecl`; the kernel
type-checks every declaration and evaluates every `… = true` (given as `Eq.refl true`) itself.
Nothing here is trusted.

* `cr_chunk k S` (after `fr_chunk k …`): `CE{k} : List Nat` (one segment: the masks exported
  by `I{k}`, padded with tautologies) and `C{k} : ∀ τ, Inp τ → SatL (rtau τ RT B) W S CE{k} 32`.
* `cr_block Name W B S data`: `NameE : List Nat` (the exported masks, in segments) and
  `Name : ∀ τ, Inp τ → SatL (rtau τ RT B) W S NameE m`.  The block's database is the
  providers' export databases, appended (`lapp`), then the local step masks; the steps are
  checked by one `sl … = true`, the exports by one `selOK … = true`.
* `cr_main Name Blk k` : `Name : unsat F` (export slot `k` of block `Blk` is the empty clause).
* `cr_tgt Name Blk k W B Wo p… 0 v… 0 t` : as `fr_tgt`, from export slot `k` of `Blk`.

Option `crup.profile` prints the kernel CPU time of each block.
-/
open Lean Elab Command
register_option crup.profile : Bool := { defValue := false, descr := "print kernel CPU time per cr_block" }

namespace CRupCmd
open FastRupCmd

/-- CPU time of this thread in ms (from /proc, 10 ms ticks), for `crup.profile` -/
def cpuTimeMs : IO Nat := do
  let st ← IO.FS.readFile "/proc/thread-self/stat"
  let f := ((st.splitOn ") ").getLast!).splitOn " "
  return (f[11]!.toNat! + f[12]!.toNat!) * 10

def natE : Expr := mkConst ``Nat
def nl (n : Nat) : Expr := mkRawNatLit n
def reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true)
def fnT : Expr := mkForall `x .default natE (mkConst ``Bool)
def listNatE : Expr := mkApp (mkConst ``List [levelZero]) natE

/-- `SatL τ' W S D n` -/
def satE (tau : Expr) (W S : Nat) (D n : Expr) : Expr :=
  mkAppN (mkConst ``CRup.SatL) #[tau, nl W, nl S, D, n]

def tautV (W : Nat) : Nat := (1 <<< 64) ||| (1 <<< (64 + W))

/-- pack masks into segments of 32 slots of `S` bits -/
def segs (S : Nat) (ms : Array Nat) : Array Nat := Id.run do
  let mut out := #[]
  let mut i := 0
  while i < ms.size do
    let mut acc := 0
    for j in [0:min 32 (ms.size - i)] do
      acc := acc ||| (ms[i + j]! <<< (j * S))
    out := out.push acc
    i := i + 32
  return out

def unsegs (S : Nat) (ss : Array Nat) : Array Nat := Id.run do
  let mut out := #[]
  for s in ss do
    for j in [0:32] do out := out.push ((s >>> (j * S)) &&& (2 ^ S - 1))
  return out

def natList (xs : Array Nat) : Expr := Id.run do
  let cons := mkApp (mkConst ``List.cons [levelZero]) natE   -- shared by every cell
  let mut e := mkApp (mkConst ``List.nil [levelZero]) natE
  for x in xs.reverse do e := mkApp2 cons (nl x) e
  return e

def listVals (e : Expr) : Array Nat := Id.run do
  let mut out := #[]
  let mut l := e
  while l.isAppOfArity ``List.cons 3 do
    out := out.push l.appFn!.appArg!.rawNatLit?.get!
    l := l.appArg!
  return out

/-- the database constant and count of a theorem `∀ τ h, SatL _ _ _ D n` -/
def provInfo (ty : Expr) : Expr × Nat :=
  let b := ty.bindingBody!.bindingBody!
  (b.appFn!.appArg!, b.appArg!.rawNatLit?.get!)

def defList (n : Name) (v : Array Nat) : CoreM Unit := do
  let val : Expr := natList v
  addDecl (Declaration.defnDecl
    { name := n, levelParams := [], type := listNatE, value := val, hints := .abbrev, safety := .safe })

def thm (n : Name) (ty val : Expr) : CoreM Unit :=
  addDecl (Declaration.thmDecl { name := n, levelParams := [], type := ty, value := val })

syntax (name := crChunk) "cr_chunk " num num : command
@[command_elab crChunk] def elabCrChunk : CommandElab := fun stx => do
  let k := stx[1].isNatLit?.get!
  let S := stx[2].isNatLit?.get!
  let ns ← getCurrNamespace
  let env ← getEnv
  let iName := ns ++ Name.mkSimple s!"I{k}"
  let some ci := env.find? iName | throwError "missing {iName}"
  let ms := exportMasks ci.type
  if ms.size > 32 then throwError "chunk larger than a segment"
  -- `msat (rtau τ RT B) W m` of the first export gives W, RT, B
  let t0 := ci.type.bindingBody!.bindingBody!.bindingBody!.bindingDomain!.bindingDomain!
  let WE := t0.appFn!.appArg!
  let rt := t0.appFn!.appFn!.appArg!
  let W := WE.rawNatLit?.get!
  let vals := (ms.map fun m => m.rawNatLit?.get!) ++ Array.replicate (32 - ms.size) (tautV W)
  let ceName := ns ++ Name.mkSimple s!"CE{k}"
  liftCoreM <| defList ceName (segs S vals)
  let CE := mkConst ceName
  let inp := mkConst (ns ++ `Inp)
  let n := ms.size
  -- under τ h e₀ … e_{n-1}: τ = bvar (n+1)
  let tauAt (j : Nat) : Expr := mkApp3 (mkConst ``FastRup.rtau) (.bvar j) rt.appFn!.appArg! rt.appArg!
  let mut pf := mkAppN (mkConst ``CRup.sat_zero) #[tauAt (n + 1), WE, nl S, CE]
  for i in [0:32] do
    let hi := if i < n then .bvar (n - 1 - i)
      else mkAppN (mkConst ``CRup.msat_taut) #[tauAt (n + 1), WE, reflTrue]
    pf := mkAppN (mkConst ``CRup.sat_succ) #[tauAt (n + 1), WE, nl S, CE, nl i, pf, hi]
  let mut lam := pf
  for i' in [0:n] do
    let i := n - 1 - i'
    lam := mkLambda (Name.mkSimple s!"e{i}") .default (mkApp3 (mkConst ``FastRup.msat) (tauAt (i + 1)) WE ms[i]!) lam
  let goal := satE (tauAt 1) W S CE (nl 32)
  let val := mkLambda `τ .default fnT (mkLambda `h .default (mkApp inp (.bvar 0))
    (mkAppN (mkConst iName) #[.bvar 1, .bvar 0, goal, lam]))
  let ty := mkForall `τ .default fnT (mkForall `h .default (mkApp inp (.bvar 0)) goal)
  liftCoreM <| thm (ns ++ Name.mkSimple s!"C{k}") ty val

/-- `cr_block Name W B S data`; data: `nP prov… nE sel… steps`.  A provider is `2k+1` (chunk
`C{k}`) or `2b` (block `B{b}`); a `sel` entry is `slot+1`, or `0` for a padding tautology
(`nE` is a multiple of 32); a step is `id pos… 0 (slot+1)… 0` (renamed positions; slots of this
block's database: the providers' exports in order, then one per step). -/
syntax (name := crBlock) "cr_block " ident num num num num* : command
@[command_elab crBlock] def elabCrBlock : CommandElab := fun stx => do
  let name := stx[1].getId
  let W := stx[2].isNatLit?.get!
  let B := stx[3].isNatLit?.get!
  let S := stx[4].isNatLit?.get!
  let xs : Array Nat := stx[5].getArgs.map fun s => s.isNatLit?.get!
  let ns ← getCurrNamespace
  let env ← getEnv
  let RT := mkConst (ns ++ `RT)
  let inp := mkConst (ns ++ `Inp)
  let tau := mkApp3 (mkConst ``FastRup.rtau) (.bvar 1) RT (nl B)   -- under τ h
  let WE := nl W
  let SE := nl S
  let nP := xs[0]!
  let provs := xs.extract 1 (1 + nP)
  let mut p := 1 + nP
  let nE := xs[p]!
  let sel := xs.extract (p + 1) (p + 1 + nE)
  p := p + 1 + nE
  if nE % 32 != 0 || nP == 0 then throwError "bad block header"
  -- providers
  let mut provE : Array (Expr × Nat × Expr) := #[]   -- database, count, proof
  let mut N := 0
  let mut vals : Array Nat := #[]      -- mask of every slot of the database
  for q in provs do
    let pn := ns ++ Name.mkSimple (if q % 2 == 1 then s!"C{q / 2}" else s!"B{q / 2}")
    let some ci := env.find? pn | throwError "missing {pn}"
    let (e, m) := provInfo ci.type
    let some (.defnInfo ei) := env.find? e.constName! | throwError "missing database {e}"
    let ss := listVals ei.value
    if m != 32 * ss.size then throwError "provider {pn}: count is not 32 * segments"
    vals := vals ++ unsegs S ss
    provE := provE.push (e, m, mkApp2 (mkConst pn) (.bvar 1) (.bvar 0))
    N := N + m
  -- local steps
  let mut masks : Array Nat := #[]
  let mut hls : Array (Array Nat) := #[]
  let mut cur : Array Nat := #[]
  let mut inHints := false
  let mut hs : Array Nat := #[]
  for k in [p:xs.size] do
    let x := xs[k]!
    if !inHints then
      if x == 0 then
        masks := masks.push (maskOf cur[0]! (cur.extract 1 cur.size))
        inHints := true; hs := #[]
      else cur := cur.push x
    else if x != 0 then hs := hs.push x
    else
      if hs.size == 0 || hs.size ≥ 65536 then throwError "step with {hs.size} hints"
      hls := hls.push hs
      inHints := false; cur := #[]
  vals := vals ++ masks
  let nS := N + masks.size
  let w := nS.log2 + 1
  let hNats := (hls.zip (Array.range hls.size)).map fun (h, k) =>
    ((h.reverse.foldl (fun acc x => (acc <<< w) ||| x) 0) <<< 64)
      ||| ((tag (k * 7919 + N) false >>> 16) <<< 16) ||| h.size
  let LE := natList (segs S masks)
  -- the database `lapp E₁ (lapp E₂ (… (lapp Eₙ L)))`, nested to the right so that walking it
  -- costs one step per segment; proofs built from the right
  let (eL, mL, pL) := provE.back!
  let mut D := mkAppN (mkConst ``CRup.lapp) #[eL, LE]
  let mut pf := mkAppN (mkConst ``CRup.sat_lapp0) #[tau, WE, SE, eL, nl mL, LE, pL, reflTrue]
  let mut cnt := mL
  for i' in [1:provE.size] do
    let (e, m, pp) := provE[provE.size - 1 - i']!
    pf := mkAppN (mkConst ``CRup.sat_lapp) #[tau, WE, SE, e, D, nl m, nl cnt, pp, pf, reflTrue]
    D := mkAppN (mkConst ``CRup.lapp) #[e, D]
    cnt := m + cnt
  let lst := natList hNats
  let wE := nl w
  let ME := nl (2 ^ w - 1)
  pf := mkAppN (mkConst ``CRup.sl_sound) #[tau, WE, SE, D, wE, ME, lst, nl N, pf, reflTrue]
  let addE := mkAppN (mkConst ``HAdd.hAdd [levelZero, levelZero, levelZero])
    #[natE, natE, natE, mkApp2 (mkConst ``instHAdd [levelZero]) natE (mkConst ``instAddNat)]
  let nAll := mkApp2 addE (nl N) (mkApp2 (mkConst ``List.length [levelZero]) natE lst)
  -- exports
  let ev := sel.map fun s => if s == 0 then tautV W else vals[s - 1]!
  let bn := ns ++ name
  let beName := ns ++ Name.mkSimple s!"{name}E"
  liftCoreM <| defList beName (segs S ev)
  let BE := mkConst beName
  pf := mkAppN (mkConst ``CRup.sel_sound) #[tau, WE, SE, D, nAll, BE, reflTrue, pf, natList sel, nl 0,
    mkAppN (mkConst ``CRup.sat_zero) #[tau, WE, SE, BE], reflTrue]
  let goal := satE tau W S BE (nl nE)
  let ty := mkForall `τ .default fnT (mkForall `h .default (mkApp inp (.bvar 0)) goal)
  let val := mkLambda `τ .default fnT (mkLambda `h .default (mkApp inp (.bvar 0)) pf)
  let prof := (← getOptions).getBool `crup.profile false
  let t0 ← if prof then cpuTimeMs else pure 0
  liftCoreM <| thm bn ty val
  let t1 ← if prof then cpuTimeMs else pure 0
  if prof then
    IO.eprintln s!"{bn}: kernel {t1 - t0} ms cpu, slots {nS}, steps {masks.size}, hints {hls.foldl (· + ·.size) 0}"

/-- `cr_main Name Blk k` : `Name : WinCNF.unsat F` from the empty clause in export slot `k`. -/
syntax (name := crMain) "cr_main " ident ident num : command
@[command_elab crMain] def elabCrMain : CommandElab := fun stx => do
  let name := stx[1].getId
  let bname := stx[2].getId
  let k := stx[3].isNatLit?.get!
  let ns ← getCurrNamespace
  let env ← getEnv
  let bn := ns ++ bname
  let some ci := env.find? bn | throwError "missing {bn}"
  let args := ci.type.bindingBody!.bindingBody!.getAppArgs   -- τ' W S E m
  let tau := mkApp3 (mkConst ``FastRup.rtau) (.bvar 1) (mkConst (ns ++ `RT)) args[0]!.appArg!
  let val := mkLambda `τ .default fnT (mkLambda `h .default (mkApp (mkConst (ns ++ `Inp)) (.bvar 0))
    (mkAppN (mkConst ``CRup.not_sat_zero) #[tau, args[1]!, args[2]!, args[3]!, args[4]!, nl k,
      mkApp2 (mkConst bn) (.bvar 1) (.bvar 0), reflTrue, reflTrue]))
  let ty := mkApp (mkConst ``WinCNF.unsat) (mkConst (ns ++ `F))
  liftCoreM <| thm name ty val

syntax (name := crTgt) "cr_tgt " ident ident num num num num num* : command

/-- `cr_tgt NAME BLOCK k W B Wo  p… 0 v… 0 t` : as `fr_tgt`, from export slot `k` of `BLOCK`. -/
@[command_elab crTgt] def elabCrTgt : CommandElab := fun stx => do
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
  let args := ci.type.bindingBody!.bindingBody!.getAppArgs   -- τ' W S E m
  let WE := nl W
  let BE := nl B
  let RT := mkConst (ns ++ `RT)
  let inp := mkConst (ns ++ `Inp)
  let cl := listE intE (ps.map (litE Wo))
  let vsE := listE natE (vs.map mkRawNatLit)
  let m := Id.run do
    let mut acc := 0
    for (p, v) in ps.zip vs do
      acc := acc ||| (1 <<< (64 + (if p < Wo then v else W + v)))
    return acc
  let tau := mkApp3 (mkConst ``FastRup.rtau) (.bvar 1) RT BE
  let M := mkAppN (mkConst ``CRup.getL) #[args[2]!, args[3]!, nl k]
  let optNat := mkApp (mkConst ``Option [levelZero]) natE
  let hs := mkAppN (mkConst ``CRup.sat_get) #[tau, WE, args[2]!, args[3]!, args[4]!, nl k,
    mkApp2 (mkConst bn) (.bvar 1) (.bvar 0), reflTrue]
  let body := mkAppN (mkConst ``FastRup.clauseSat_of_msatT)
    #[.bvar 1, WE, RT, BE, cl, vsE, nl m, nl tg, M,
      mkApp2 (mkConst ``Eq.refl [levelOne]) optNat (mkApp2 (mkConst ``Option.some [levelZero]) natE (nl m)),
      reflTrue, reflTrue, hs]
  let goal := mkApp2 (mkConst ``WinCNF.clauseSat) (.bvar 1) cl
  let ty := mkForall `τ .default fnT (mkForall `h .default (mkApp inp (.bvar 0)) goal)
  let val := mkLambda `τ .default fnT (mkLambda `h .default (mkApp inp (.bvar 0)) body)
  liftCoreM <| thm (ns ++ name) ty val

end CRupCmd
