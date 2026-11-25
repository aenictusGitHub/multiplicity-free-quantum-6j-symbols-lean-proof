import OccupationTensorCoefficients
import InjectedBasisSynthesis

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def occupationTensorSynthesis (n l m : ℕ) :
    (((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)) →₀ ℝ) →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact injectedBasisSynthesis (K:=ℝ) (V:=V)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) (occupationPairEmbedding n l m)

theorem occupationTensorSynthesis_coefficients (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    occupationTensorSynthesis n l m (occupationTensorCoefficients n l m v)=v := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact injectedBasisSynthesis_coefficients (K:=ℝ) (V:=V)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m))
    (occupationPairEmbedding n l m) (occupationPairEmbedding_injective n l m) v

theorem occupationTensorCoefficients_synthesis (n l m : ℕ)
    (f : ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)) →₀ ℝ)
    (hf : ∀ x y,f (x,y)≠0 → x∈occupationWeights (Fin (n+1)) l ∧ y∈occupationWeights (Fin (n+1)) m) :
    occupationTensorCoefficients n l m (occupationTensorSynthesis n l m f)=f := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  apply injectedBasisCoefficients_synthesis (K:=ℝ) (V:=V)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) _ (occupationPairEmbedding_injective n l m)
  intro p hp
  have hs:=hf p.1 p.2 hp
  exact ⟨(⟨p.1,hs.1⟩,⟨p.2,hs.2⟩),rfl⟩

end AMSPhysical
