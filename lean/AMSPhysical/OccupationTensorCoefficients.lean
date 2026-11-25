import QuantumOccupationGraph
import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def occupationPairEmbedding (n l m : ℕ)
    (p : occupationWeights (Fin (n+1)) l × occupationWeights (Fin (n+1)) m) :
    (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ) := (p.1.val,p.2.val)

theorem occupationPairEmbedding_injective (n l m : ℕ) :
    Function.Injective (occupationPairEmbedding n l m) := by
  intro p z he
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst he)
  · exact Subtype.ext (congrArg Prod.snd he)

/-- Extend the literal coefficients of an actual finite tensor vector by zero
to the unrestricted pair lattice. Negative occupations have zero coefficient. -/
def occupationTensorCoefficients (n l m : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) →ₗ[ℝ]
      (((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)) →₀ ℝ) :=
  (Finsupp.lmapDomain ℝ ℝ (occupationPairEmbedding n l m)).comp
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).repr.toLinearMap

theorem occupationTensorCoefficients_basis (n l m : ℕ)
    (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    occupationTensorCoefficients n l m
      (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m y)=
      Finsupp.single (x.val,y.val) 1 := by
  rw [← Module.Basis.tensorProduct_apply' (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m) (x,y)]
  change Finsupp.mapDomain (occupationPairEmbedding n l m)
    (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).repr
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) (x,y)))=_
  rw [Module.Basis.repr_self,Finsupp.mapDomain_single]
  rfl

theorem occupationTensorCoefficients_repr (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    occupationTensorCoefficients n l m v (x.val,y.val)=
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).repr v) (x,y) :=
  Finsupp.mapDomain_apply (occupationPairEmbedding_injective n l m) _ (x,y)

theorem occupationTensorCoefficients_injective (n l m : ℕ) :
    Function.Injective (occupationTensorCoefficients n l m) := by
  intro v w he
  apply ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).repr.injective
  exact Finsupp.mapDomain_injective (occupationPairEmbedding_injective n l m) he

theorem occupationTensorCoefficients_support (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (x y : Fin (n+1) → ℤ) (h : occupationTensorCoefficients n l m v (x,y)≠0) :
    x∈occupationWeights (Fin (n+1)) l ∧ y∈occupationWeights (Fin (n+1)) m := by
  by_contra hn
  have hr : (x,y)∉Set.range (occupationPairEmbedding n l m) := by
    rintro ⟨p,hp⟩
    apply hn
    have hx : p.1.val=x := congrArg Prod.fst hp
    have hy : p.2.val=y := congrArg Prod.snd hp
    exact ⟨hx ▸ p.1.property,hy ▸ p.2.property⟩
  exact h (Finsupp.mapDomain_notin_range _ _ hr)

end AMSPhysical
