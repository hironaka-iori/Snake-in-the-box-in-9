import Boxes

namespace Snake9.Boxes88

/-- Stored nonterminal rows contain a depth followed by six child indices.
Indices zero and one are the two constant leaves. -/
abbrev Diagram := Array (Array Nat)

def nextNode (g : Diagram) (node symbol : Nat) : Nat :=
  if node < 2 then node else (g.getD (node-2) #[]).getD symbol 0

def diagramEval (g : Diagram) : Nat → List Nat → Bool
  | node, [] => node == 1
  | node, symbol :: suffix => diagramEval g (nextNode g node symbol) suffix

theorem diagram_one (g : Diagram) (symbols : List Nat) : diagramEval g 1 symbols = true := by
  induction symbols with
  | nil => rfl
  | cons x xs ih => simpa [diagramEval,nextNode] using ih

inductive CoverTree where
  | accept
  | reject (boxIndex : Nat)
  | split (children : List CoverTree)
  deriving Repr

/-- An accepted diagram leaf or a proved forbidden box closes a branch.
Otherwise split into all six possible next count symbols. -/
def checkCover (g : Diagram) (boxes : List Box) :
    Nat → List Nat → Nat → CoverTree → Bool
  | _, _, node, .accept => node == 1
  | _, pref, _, .reject i => decide (i < boxes.length) && coversPrefix (boxes.getD i []) pref
  | 0, _, _, .split _ => false
  | fuel+1, pref, node, .split children =>
      decide (children.length = 6) && (List.range 6).all fun j =>
        checkCover g boxes fuel (pref ++ [j+1]) (nextNode g node (j+1))
          (children.getD j .accept)

theorem reject_prefix_sound (boxes : List Box) (pref suffix : List Nat) (i : Nat)
    (hi : i < boxes.length) (hc : coversPrefix (boxes.getD i []) pref = true)
    (hlen : (pref ++ suffix).length = 6)
    (hvalid : ∀ x ∈ pref ++ suffix, 1 ≤ x ∧ x ≤ 6) :
    ∃ b ∈ boxes, inside b (fun j => (pref ++ suffix).getD j 0) := by
  refine ⟨boxes.getD i [], ?_, ?_⟩
  · simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
      using (List.getElem_mem hi : boxes[i] ∈ boxes)
  · apply coversPrefix_sound _ pref _ hc
    · intro j hj
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hj]
    · intro j hj
      have hj' : j < (pref ++ suffix).length := by omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some]
      exact hvalid _ (List.getElem_mem hj')

theorem checkCover_sound (g : Diagram) (boxes : List Box) (fuel : Nat)
    (pref : List Nat) (node : Nat) (certificate : CoverTree)
    (hc : checkCover g boxes fuel pref node certificate = true)
    (suffix : List Nat) (hlen : suffix.length = fuel)
    (htotal : pref.length+fuel = 6)
    (hvalid : ∀ x ∈ pref ++ suffix, 1 ≤ x ∧ x ≤ 6) :
    diagramEval g node suffix = true ∨
      ∃ b ∈ boxes, inside b (fun j => (pref ++ suffix).getD j 0) := by
  induction fuel using Nat.strong_induction_on generalizing pref node certificate suffix with
  | h fuel ih =>
    cases certificate with
    | accept =>
      have hn : node = 1 := by simpa only [checkCover, beq_iff_eq] using hc
      subst node
      exact Or.inl (diagram_one g suffix)
    | reject i =>
      simp only [checkCover] at hc
      have hh := Bool.and_eq_true_iff.mp hc
      exact Or.inr (reject_prefix_sound boxes pref suffix i (of_decide_eq_true hh.1)
        hh.2 (by simp only [List.length_append]; omega) hvalid)
    | split children =>
      cases fuel with
      | zero => simp [checkCover] at hc
      | succ n =>
        cases suffix with
        | nil => simp at hlen
        | cons x xs =>
          have hx : 1 ≤ x ∧ x ≤ 6 := hvalid x (by simp)
          have hxrange : x-1 < 6 := by omega
          have hxsucc : x-1+1 = x := by omega
          have htests := (Bool.and_eq_true_iff.mp hc).2
          have hchild := List.all_eq_true.mp htests (x-1) (List.mem_range.mpr hxrange)
          simp only [hxsucc] at hchild
          have hlen' : xs.length = n := by simpa using hlen
          have htotal' : (pref ++ [x]).length+n = 6 := by simp only [List.length_append,List.length_singleton]; omega
          have hv' : ∀ y ∈ (pref ++ [x]) ++ xs, 1 ≤ y ∧ y ≤ 6 := by
            simpa only [List.append_assoc,List.singleton_append] using hvalid
          have result := ih n (by omega) (pref ++ [x]) (nextNode g node x)
            (children.getD (x-1) .accept) hchild xs hlen' htotal' hv'
          simpa only [diagramEval,List.append_assoc,List.singleton_append] using result

/-- When all certificate boxes are forbidden, the diagram accepts every candidate. -/
theorem cover_implies_membership (g : Diagram) (boxes : List Box) (node : Nat)
    (certificate : CoverTree) (hc : checkCover g boxes 6 [] node certificate = true)
    (symbols : List Nat) (hlen : symbols.length = 6)
    (hvalid : ∀ x ∈ symbols, 1 ≤ x ∧ x ≤ 6)
    (havoid : ∀ b ∈ boxes, ¬ inside b (fun j => symbols.getD j 0)) :
    diagramEval g node symbols = true := by
  have h := checkCover_sound g boxes 6 [] node certificate hc symbols hlen rfl (by simpa using hvalid)
  rcases h with h | ⟨b,hb,hh⟩
  · exact h
  · exact (havoid b hb (by simpa using hh)).elim

#print axioms diagram_one
#print axioms reject_prefix_sound
#print axioms checkCover_sound
#print axioms cover_implies_membership
end Snake9.Boxes88
