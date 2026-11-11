import AttachmentBalance191
import AlternatingCounts191
namespace MovingEndpoints192
open Replacement191

theorem attachmentCorrection {V : Type} (neighbours : List V) (p q : V → Bool)
    (oldEndpoint newEndpoint : Nat)
    (degree : count neighbours p+oldEndpoint=count neighbours q+newEndpoint) :
    count neighbours (fun v => q v && !p v)+newEndpoint =
      count neighbours (fun v => p v && !q v)+oldEndpoint := by
  have hp := countPartition neighbours p q
  have hq := countPartition neighbours q p
  have hc := intersectionSymmetric neighbours p q
  omega

theorem oldEndpointBecomesInternal {V : Type} (neighbours : List V) (p q : V → Bool)
    (degree : count neighbours p+1=count neighbours q) :
    count neighbours (fun v => q v && !p v) =
      count neighbours (fun v => p v && !q v)+1 := by
  exact attachmentCorrection neighbours p q 1 0 (by omega)

theorem oddColourCount (k : Nat) (f : Nat → Nat)
    (halt : ∀ i, i+1 < 2*k+1 → f i+f (i+1)=1) :
    colourSum f (2*k+1)=k+f (2*k) := by
  have h := alternatingColourCount k f (by intro i hi; exact halt i (by omega))
  change colourSum f (2*k)+f (2*k)=k+f (2*k)
  rw [h]

theorem gain191to192 (f g : Nat → Nat)
    (hf : ∀ i, i+1 < 192 → f i+f (i+1)=1)
    (hg : ∀ i, i+1 < 193 → g i+g (i+1)=1) :
    colourSum g 193=colourSum f 192+g 192 := by
  have h1 := alternatingColourCount 96 f hf
  have h2 := oddColourCount 96 g hg
  change colourSum f 192=96 at h1
  change colourSum g 193=96+g 192 at h2
  omega

#print axioms attachmentCorrection
#print axioms oldEndpointBecomesInternal
#print axioms oddColourCount
#print axioms gain191to192
end MovingEndpoints192
