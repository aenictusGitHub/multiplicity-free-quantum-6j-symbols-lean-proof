import QuantumCreationCartan
import QuantumMixedCoefficientRaising
import QuantumTypeAIntertwiner
import QuantumOccupationShifts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The actual degree-raising map on the finite physical occupation spaces. -/
def mixedFiniteCreation (q : ℝ) (n l m : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) :=
  (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).constr ℝ)
    (fun p =>∑ k : Fin (n+1),mixedCreationCoefficient q n k (p.1.val,p.2.val) •
      (quantumOccupationBasis (K:=ℝ) (l+1) (shiftedOccupation n l 1 k p.1) ⊗ₜ[ℝ]
        quantumOccupationBasis (K:=ℝ) (m+1) (shiftedOccupation n m 1 k p.2)))

theorem mixedFiniteCreation_basis (q : ℝ) (n l m : ℕ)
    (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    mixedFiniteCreation q n l m (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m y)=
      ∑ k : Fin (n+1),mixedCreationCoefficient q n k (x.val,y.val) •
        (quantumOccupationBasis (K:=ℝ) (l+1) (shiftedOccupation n l 1 k x) ⊗ₜ[ℝ]
          quantumOccupationBasis (K:=ℝ) (m+1) (shiftedOccupation n m 1 k y)) := by
  rw [← Module.Basis.tensorProduct_apply' (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m) (x,y)]
  exact Module.Basis.constr_basis _ _ _ _

theorem occupationTensorCoefficients_creation (q : ℝ) (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    occupationTensorCoefficients n (l+1) (m+1) (mixedFiniteCreation q n l m v)=
      pairLatticeCreation q n (occupationTensorCoefficients n l m v) := by
  have he : (occupationTensorCoefficients n (l+1) (m+1)).comp (mixedFiniteCreation q n l m)=
      (pairLatticeCreation q n).comp (occupationTensorCoefficients n l m) := by
    apply ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).ext
    intro p
    simp only [LinearMap.comp_apply,Module.Basis.tensorProduct_apply',mixedFiniteCreation_basis,
      map_sum,map_smul,occupationTensorCoefficients_basis,pairLatticeCreation,LinearMap.sum_apply,
      weightedTranslation_single,Finsupp.smul_single,smul_eq_mul,mul_one,one_mul]
    rfl
  exact DFunLike.congr_fun he v

/-- Raising commutation now concerns the independently constructed finite
physical modules, not merely an unrestricted coefficient recurrence. -/
theorem mixedFiniteCreation_intertwines_E (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m : ℕ) (i : Fin n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    mixedFiniteCreation q n l m (typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 0) v)=
      typeAMixedTensor q hq hD n (l+1) (m+1) (typeAAlgebraGenerator q n i 0) (mixedFiniteCreation q n l m v) := by
  apply occupationTensorCoefficients_injective n (l+1) (m+1)
  rw [occupationTensorCoefficients_creation,occupationTensorCoefficients_mixed_E,
    occupationTensorCoefficients_mixed_E,occupationTensorCoefficients_creation]
  exact DFunLike.congr_fun (pairLatticeCreation_commutes_raising q hq hD n i) _

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteCreation_intertwines_E
