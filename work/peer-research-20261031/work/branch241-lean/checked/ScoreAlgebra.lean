import Std
import Lean.Elab.Tactic.Omega

/-!
Algebraic parts of the new Q9 score argument.
No geometric assumptions are silently imported. In particular scoreGap23
ASSUMES the cap-21 exclusion; it is not a Lean proof of that exclusion.
All finite arithmetic below uses kernel reduction, never native_decide.
-/
namespace Q9Score

/-- Finite coefficient lemma after clearing the positive denominator 63*h*t.
    h=1..7; t=1..3. The indicators preserve the occupancy bonus. -/
theorem scalar_share : ∀ h : Fin 7, ∀ t : Fin 3,
    (h.val + 1) * (t.val + 1) *
      (13 - (h.val + 1) +
        3 * (if t.val + 1 ≤ 2 then 1 else 0) +
        9 * (if t.val + 1 = 1 then 1 else 0)) ≤ 126 := by
  decide +kernel

/-- The integer support inequality used by the original r6 score. -/
theorem support_r6 : ∀ h : Fin 7,
    (h.val + 1) * (13 - (h.val + 1)) ≤ 42 := by
  decide +kernel

/-- The double-counting consequences leave no possible integer score 22.
    The actual geometric realization of these premises is a separate obligation. -/
theorem scoreGap23 (alpha e2 e3 bonus : Nat)
    (singleton : 1 ≤ alpha)
    (emptyCubeCount : 3 * e3 ≤ 6 * e2)
    (bonusCount : bonus ≤ 4 * e2)
    (cap21Excluded : 22 ≤ 21 * alpha + 2 * e2 + e3 + bonus) :
    23 ≤ 21 * alpha + 2 * e2 + e3 + bonus := by
  by_cases h : 23 ≤ 21 * alpha + 2 * e2 + e3 + bonus
  · exact h
  · have upper : 21 * alpha + 2 * e2 + e3 + bonus ≤ 22 := by omega
    have az : alpha = 1 := by omega
    have ez : e2 = 0 := by omega
    have cz : e3 = 0 := by omega
    have bz : bonus = 0 := by omega
    omega

/-- Pure algebra of the square incidence identity for nontrivial paths.
    Counts and s3=v-2 have NOT been postulated as axioms: they are explicit inputs. -/
theorem incidenceIdentity (v s0 s1 s2 s3 : Nat)
    (nontrivial : 2 ≤ v)
    (squareCount : s0 + s1 + s2 + s3 = 4608)
    (vertexCount : s1 + 2 * s2 + 3 * s3 = 36 * v)
    (threePointSquares : s3 = v - 2) :
    s1 + 2 * s0 + 35 * v = 9214 := by
  omega

/-- Necessary aggregate inequality at triple threshold 255 excludes v>=236.
    This theorem DOES NOT prove the assumed triple threshold. -/
theorem conditional234 (v : Nat)
    (necessary : 735 * v + 255 * ((v - 2) / 3) +
      22 * ((v - 2) % 3) ≤ 193326) : v ≤ 235 := by
  omega

/-- Threshold 267 suffices for the 233-edge target; 268 is unnecessary. -/
theorem conditional233 (v : Nat)
    (necessary : 735 * v + 267 * ((v - 2) / 3) +
      22 * ((v - 2) % 3) ≤ 193326) : v ≤ 234 := by
  omega

/-- Stronger single-vertex remainder bound remains sufficient. -/
theorem conditional233_remainder23 (v : Nat)
    (necessary : 735 * v + 267 * ((v - 2) / 3) +
      23 * ((v - 2) % 3) ≤ 193326) : v ≤ 234 := by
  omega

theorem margin234 :
    735 * 236 + 255 * ((236 - 2) / 3) + 22 * ((236 - 2) % 3) =
      193326 + 24 := by decide +kernel

theorem margin233 :
    735 * 235 + 267 * ((235 - 2) / 3) + 22 * ((235 - 2) % 3) =
      193326 + 2 := by decide +kernel

#print axioms scalar_share
#print axioms support_r6
#print axioms scoreGap23
#print axioms incidenceIdentity
#print axioms conditional234
#print axioms conditional233
#print axioms conditional233_remainder23
#print axioms margin234
#print axioms margin233
end Q9Score
