import Boxes
import DigitReconstruction

namespace Snake9.Boxes88
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.GraphInterpretation75 Snake9.Guards79 Snake9.ShortRules81
open Snake9.History84 Snake9.Reference85 Snake9.Retained87
open Snake9.Direction77
set_option maxHeartbeats 2000000

inductive Witness where
  | reference (keyIndex offset : Nat) (reverse : Bool)
  | short (ruleIndex offset : Nat) (reverse : Bool)
  | interval (keyIndex offset : Nat) (reverse : Bool)
  | history (ruleIndex : Nat)
  deriving Repr, DecidableEq

def oriented (reverse : Bool) (xs : List Nat) : List Nat :=
  if reverse then xs.reverse else xs

def referenceBoxValid (ds : List Nat) (b : Box) (ki s : Nat) (reverse : Bool) : Bool :=
  let k := referenceKeys.getD ki ([],[])
  decide (ki < referenceKeys.length) && (decide (2 ≤ k.2.length ∧ s+k.2.length ≤ 6) &&
    ((canon (oriented reverse ((ds.drop (s+2)).take (k.2.length+1))) == k.1) &&
    (List.range k.2.length).all fun i => decide
      ((b.getD (s+i) (1,6)).1 = (oriented reverse k.2).getD i 0 ∧
       (b.getD (s+i) (1,6)).2 = (oriented reverse k.2).getD i 0)))

def shortBoxValid (ds : List Nat) (b : Box) (ki offset : Nat) (reverse : Bool) : Bool :=
  let rule := shortRules.getD ki ([],.caps [])
  decide (ki < shortRules.length ∧ offset < 10) &&
    (decide (offset+rule.1.length ≤ 9) &&
    ((rule.2.positions.all fun j => decide
      (3 ≤ offset+orientedPosition rule.1.length reverse j ∧
       offset+orientedPosition rule.1.length reverse j ≤ 8)) &&
    ((canon (oriented reverse ((ds.drop offset).take rule.1.length)) == rule.1) &&
    encodedBadB rule.2 (fun j => (b.getD
      (offset+orientedPosition rule.1.length reverse j-3) (1,6)).2))))

def intervalBoxValid (ds : List Nat) (b : Box) (ki s : Nat) (reverse : Bool) : Bool :=
  let key := intervalKeys72.getD ki ([],[])
  decide (ki < intervalKeys72.length ∧ s < 3 ∧ key.2.length = 4) &&
    ((canon (oriented reverse ((ds.drop (s+2)).take 5)) == key.1) &&
    (List.range key.2.length).all fun i =>
      let j := s + if reverse then 4-1-i else i
      decide (j < 6 ∧ (key.2.getD i (0,21)).1 ≤ (b.getD j (1,6)).1 ∧
        (b.getD j (1,6)).2 ≤ (key.2.getD i (0,21)).2))

def historyBoxValid (q di : Nat) (b : Box) (ki : Nat) : Bool :=
  let rule := historyRules.getD ki ([],0)
  let hist := Snake9.History75.prefixes.getD q [] ++ [di]
  decide (ki < historyRules.length ∧ rule.2 < 6) &&
    (decide (3 ≤ hist.length) && ((hist.drop (hist.length-3) == rule.1) &&
    decide ((b.getD rule.2 (1,6)).2 ≤ 2)))

/-- The decoded direction index is exactly the one used inside numericKeep. -/
def boxWitnessValid (q di : Nat) (b : Box) (w : Witness) : Bool :=
  decide (b.length = 6 ∧ q < 75 ∧ di < 505) &&
    let ds := extensions.getD di []
    match w with
    | .reference ki s reverse => referenceBoxValid ds b ki s reverse
    | .short ki s reverse => shortBoxValid ds b ki s reverse
    | .interval ki s reverse => intervalBoxValid ds b ki s reverse
    | .history ki => historyBoxValid q (extensions.idxOf ds) b ki

theorem lookup_mem {α : Type} (xs : List α) (i : Nat) (d : α) (hi : i < xs.length) :
    xs.getD i d ∈ xs := by
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using
    (List.getElem_mem hi : xs[i] ∈ xs)

theorem sum_map_mono (xs : List Nat) (f g : Nat → Nat)
    (h : ∀ j ∈ xs, f j ≤ g j) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun j hj => h j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    omega

theorem encodedBadB_mono (test : CountTest) (f g : Nat → Nat)
    (hfg : ∀ j ∈ test.positions, f j ≤ g j) (hg : encodedBadB test g = true) :
    encodedBadB test f = true := by
  rw [encodedBadB_iff] at hg ⊢
  cases test with
  | caps bounds =>
    intro b hb
    have hh := hfg b.1 (by
      change b.1 ∈ bounds.map Prod.fst
      exact List.mem_map.mpr ⟨b,hb,rfl⟩)
    exact le_trans hh (hg b hb)
  | sum positions cap =>
    refine ⟨le_trans (sum_map_mono positions f g hfg) hg.1, ?_⟩
    intro j hj
    exact lt_of_le_of_lt (hfg j hj) (hg.2 j hj)

theorem referenceBoxValid_sound (ds : List Nat) (b : Box) (ki s code : Nat)
    (reverse : Bool) (hc : code < 46656)
    (hv : referenceBoxValid ds b ki s reverse = true)
    (hin : inside b (digit code)) (hk : referenceKeep ds code = true) : False := by
  let k := referenceKeys.getD ki ([],[])
  have h : ki < referenceKeys.length ∧ (2 ≤ k.2.length ∧ s+k.2.length ≤ 6) ∧
      canon (oriented reverse ((ds.drop (s+2)).take (k.2.length+1))) = k.1 ∧
      (∀ i, i < k.2.length → (b.getD (s+i) (1,6)).1 = (oriented reverse k.2).getD i 0 ∧
        (b.getD (s+i) (1,6)).2 = (oriented reverse k.2).getD i 0) := by
    simpa only [referenceBoxValid, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, List.all_eq_true, List.mem_range] using hv
  have hlen : (oriented reverse k.2).length = k.2.length := by
    cases reverse <;> simp [oriented]
  have heq : code / 6^(6-s-k.2.length) % 6^k.2.length =
      encodeCounts (oriented reverse k.2) 0 := by
    simpa only [hlen] using digit_slice_code code s (oriented reverse k.2) hc
      (by simpa only [hlen] using h.2.1.1) (by simpa only [hlen] using h.2.1.2)
      (by
        intro i hi
        have hi' : i < k.2.length := by simpa only [hlen] using hi
        have hb := hin (s+i) (by omega)
        have he := h.2.2.2 i hi'
        omega)
  have hm : k ∈ referenceKeys := lookup_mem referenceKeys ki ([],[]) h.1
  have ht := List.all_eq_true.mp (List.all_eq_true.mp hk k hm) s
    (List.mem_range.mpr (by omega))
  have hit : (referenceForwardB ds code s k || referenceReverseB ds code s k) = true := by
    cases reverse
    · apply Bool.or_eq_true_iff.mpr; left
      simpa only [referenceForwardB, Bool.and_eq_true, beq_iff_eq, oriented, Bool.false_eq_true,
        ↓reduceIte] using And.intro h.2.2.1 heq
    · apply Bool.or_eq_true_iff.mpr; right
      simpa only [referenceReverseB, Bool.and_eq_true, beq_iff_eq, oriented,
        ↓reduceIte] using And.intro h.2.2.1 heq
  simp only [h.2.1.2, ↓reduceIte, hit, Bool.not_true] at ht
  exact Bool.noConfusion ht

theorem shortBoxValid_sound (ds : List Nat) (b : Box) (ki offset code : Nat)
    (reverse : Bool) (hv : shortBoxValid ds b ki offset reverse = true)
    (hin : inside b (digit code)) (hk : shortKeep ds code = true) : False := by
  let rule := shortRules.getD ki ([],.caps [])
  have h : (ki < shortRules.length ∧ offset < 10) ∧ offset+rule.1.length ≤ 9 ∧
      (∀ j ∈ rule.2.positions, 3 ≤ offset+orientedPosition rule.1.length reverse j ∧
        offset+orientedPosition rule.1.length reverse j ≤ 8) ∧
      canon (oriented reverse ((ds.drop offset).take rule.1.length)) = rule.1 ∧
      encodedBadB rule.2 (fun j => (b.getD
        (offset+orientedPosition rule.1.length reverse j-3) (1,6)).2) = true := by
    simpa only [shortBoxValid, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, List.all_eq_true] using hv
  have hb := encodedBadB_mono rule.2
    (fun j => digit code (offset+orientedPosition rule.1.length reverse j-3))
    (fun j => (b.getD (offset+orientedPosition rule.1.length reverse j-3) (1,6)).2)
    (by intro j hj; exact (hin _ (by have := h.2.2.1 j hj; omega)).2) h.2.2.2.2
  have hit : shortHitB ds code offset reverse rule = true := by
    simpa only [shortHitB, oriented, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, List.all_eq_true] using
      And.intro h.2.1 (And.intro h.2.2.1 (And.intro h.2.2.2.1 hb))
  have hm : rule ∈ shortRules := lookup_mem shortRules ki ([],.caps []) h.1.1
  have ht := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hk rule hm)
    offset (List.mem_range.mpr h.1.2)) reverse (by cases reverse <;> simp)
  simp only [hit, Bool.not_true] at ht
  exact Bool.noConfusion ht

theorem intervalBoxValid_sound (ds : List Nat) (b : Box) (ki s code : Nat)
    (reverse : Bool) (hv : intervalBoxValid ds b ki s reverse = true)
    (hin : inside b (digit code)) (hk : intervalKeep ds code = true) : False := by
  let key := intervalKeys72.getD ki ([],[])
  have h : (ki < intervalKeys72.length ∧ s < 3 ∧ key.2.length = 4) ∧
      canon (oriented reverse ((ds.drop (s+2)).take 5)) = key.1 ∧
      (∀ i, i < key.2.length →
        let j := s + if reverse then 4-1-i else i
        j < 6 ∧ (key.2.getD i (0,21)).1 ≤ (b.getD j (1,6)).1 ∧
          (b.getD j (1,6)).2 ≤ (key.2.getD i (0,21)).2) := by
    simpa only [intervalBoxValid, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, List.all_eq_true, List.mem_range] using hv
  have hh : intervalHitB code s 4 reverse key.2 = true := by
    apply List.all_eq_true.mpr
    intro i hi
    apply decide_eq_true
    have hh := h.2.2 i (List.mem_range.mp hi)
    have hb := hin _ hh.1
    exact ⟨le_trans hh.2.1 hb.1, le_trans hb.2 hh.2.2⟩
  have hit : intervalRuleHitB ds code s key = true := by
    cases reverse
    · apply Bool.or_eq_true_iff.mpr; left
      simpa only [Bool.and_eq_true, beq_iff_eq, oriented, Bool.false_eq_true, ↓reduceIte]
        using And.intro h.2.1 hh
    · apply Bool.or_eq_true_iff.mpr; right
      simpa only [Bool.and_eq_true, beq_iff_eq, oriented, ↓reduceIte]
        using And.intro h.2.1 hh
  have hm : key ∈ intervalKeys72 := lookup_mem intervalKeys72 ki ([],[]) h.1.1
  have ht := List.all_eq_true.mp (List.all_eq_true.mp hk key hm) s (List.mem_range.mpr h.1.2.1)
  simp only [hit, Bool.not_true] at ht
  exact Bool.noConfusion ht

theorem historyBoxValid_sound (q di : Nat) (b : Box) (ki code : Nat)
    (hv : historyBoxValid q di b ki = true)
    (hin : inside b (digit code)) (hk : historyKeep q di code = true) : False := by
  let rule := historyRules.getD ki ([],0)
  let hist := Snake9.History75.prefixes.getD q [] ++ [di]
  have h : (ki < historyRules.length ∧ rule.2 < 6) ∧ 3 ≤ hist.length ∧
      hist.drop (hist.length-3) = rule.1 ∧ (b.getD rule.2 (1,6)).2 ≤ 2 := by
    simpa only [historyBoxValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using hv
  have hb := hin rule.2 h.1.2
  have hit : historyHitB q di code rule = true := by
    simpa only [historyHitB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using
      And.intro h.2.1 (And.intro h.2.2.1 (le_trans hb.2 h.2.2.2))
  have ht := List.all_eq_true.mp hk rule (lookup_mem historyRules ki ([],0) h.1.1)
  simp only [hit, Bool.not_true] at ht
  exact Bool.noConfusion ht

theorem boxWitnessValid_sound (q di code : Nat) (b : Box) (w : Witness)
    (hc : code < 46656) (hv : boxWitnessValid q di b w = true)
    (hk : numericKeep q di code = true) : ¬inside b (digit code) := by
  intro hin
  have h := (Bool.and_eq_true_iff.mp hv).2
  have k := hk
  simp only [numericKeep, wordKeep, Bool.and_eq_true] at k
  cases w with
  | reference ki s reverse => exact referenceBoxValid_sound _ b ki s code reverse hc h hin k.2.1
  | short ki s reverse => exact shortBoxValid_sound _ b ki s code reverse h hin k.2.2.1
  | interval ki s reverse => exact intervalBoxValid_sound _ b ki s code reverse h hin k.2.2.2.2
  | history ki => exact historyBoxValid_sound q _ b ki code h hin k.2.2.2.1

#print axioms lookup_mem
#print axioms sum_map_mono
#print axioms encodedBadB_mono
#print axioms referenceBoxValid_sound
#print axioms shortBoxValid_sound
#print axioms intervalBoxValid_sound
#print axioms historyBoxValid_sound
#print axioms boxWitnessValid_sound
end Snake9.Boxes88
