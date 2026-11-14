import Capacity209

/-!
Source prepared for checking; not compiled by its author.

F lists distinct variables already forced to be exceptions.
E lists the actual exceptions of a fixed complete assignment.
The geometric meaning of exception and partner support is supplied
by the explicit membership and unsupported-value hypotheses below.
-/

namespace SpareSupport212

/-- More distinct forced exceptions than the permitted number
contradict an actual exception list containing them. -/
theorem too_many_forced (F E : List Nat) (s : Nat)
    (hF : F.Nodup)
    (hsubset : ∀ x, x ∈ F → x ∈ E)
    (hcapacity : E.length ≤ s)
    (htoomany : s < F.length) : False := by
  have hbound := Capacity209.distinct_length_le F E hF hsubset
  omega

/-- Once the distinct forced exceptions exhaust capacity, every
actual exception belongs to the forced list. -/
theorem saturated_exception_cover (F E : List Nat) (s : Nat)
    (hF : F.Nodup)
    (hsubset : ∀ x, x ∈ F → x ∈ E)
    (hcapacity : E.length ≤ s)
    (hsaturated : F.length = s) :
    ∀ x, x ∈ E → x ∈ F := by
  have hbound := Capacity209.distinct_length_le F E hF hsubset
  have hlength : F.length = E.length := by omega
  exact Capacity209.saturated_covers F E hF hsubset hlength

/-- A variable outside the saturated forced list must use a supported
word if an unsupported actual value would make it an exception. -/
theorem supported_value (F E support : List Nat) (s chosen word : Nat)
    (hF : F.Nodup)
    (hsubset : ∀ x, x ∈ F → x ∈ E)
    (hcapacity : E.length ≤ s)
    (hsaturated : F.length = s)
    (hchosen : chosen ∉ F)
    (hunsupported : word ∉ support → chosen ∈ E) :
    word ∈ support := by
  by_cases hs : word ∈ support
  · exact hs
  · have hexception := hunsupported hs
    have hforced :=
      saturated_exception_cover F E s hF hsubset hcapacity hsaturated
        chosen hexception
    exact False.elim (hchosen hforced)

/-- Filtering the chosen variable's domain to supported words retains
the same complete assignment. All other domains are unchanged. -/
theorem support_filter_preserves_assignment
    (F E support : List Nat) (s chosen : Nat)
    (values : Nat → Nat) (domains : Nat → List Nat)
    (hF : F.Nodup)
    (hsubset : ∀ x, x ∈ F → x ∈ E)
    (hcapacity : E.length ≤ s)
    (hsaturated : F.length = s)
    (hchosen : chosen ∉ F)
    (hunsupported : values chosen ∉ support → chosen ∈ E)
    (hfit : ∀ g, values g ∈ domains g) :
    ∀ g, values g ∈
      (if g = chosen then
        (domains g).filter (fun word => decide (word ∈ support))
      else domains g) := by
  have hs : values chosen ∈ support :=
    supported_value F E support s chosen (values chosen)
      hF hsubset hcapacity hsaturated hchosen hunsupported
  intro g
  by_cases hg : g = chosen
  · subst g
    simpa [hs] using hfit chosen
  · simpa [hg] using hfit g

#print axioms too_many_forced
#print axioms saturated_exception_cover
#print axioms supported_value
#print axioms support_filter_preserves_assignment

end SpareSupport212
