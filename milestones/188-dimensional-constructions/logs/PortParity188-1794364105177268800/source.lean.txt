import Std
namespace Dimensional188

theorem alternatingParity (n : Nat) (f : Nat → Nat)
    (hb : ∀ i, i ≤ n → f i < 2)
    (hf : ∀ i, i < n → f i + f (i+1) = 1) :
    (f n+n)%2=f 0 := by
  induction n with
  | zero => have h := hb 0 (by omega); omega
  | succ n ih =>
    have h := ih (by intro i hi; exact hb i (by omega))
      (by intro i hi; exact hf i (by omega))
    have hn := hf n (by omega)
    have hb0 := hb n (by omega)
    have hb1 := hb (n+1) (by omega)
    omega

theorem fixedEndpointParity (m n : Nat) (f g : Nat → Nat)
    (hfm : ∀ i, i ≤ m → f i < 2)
    (hfn : ∀ i, i < m → f i+f (i+1)=1)
    (hgm : ∀ i, i ≤ n → g i < 2)
    (hgn : ∀ i, i < n → g i+g (i+1)=1)
    (hstart : f 0=g 0) (hend : f m=g n) : m%2=n%2 := by
  have h1 := alternatingParity m f hfm hfn
  have h2 := alternatingParity n g hgm hgn
  have hb := hfm m (by omega)
  omega

#print axioms alternatingParity
#print axioms fixedEndpointParity
end Dimensional188
