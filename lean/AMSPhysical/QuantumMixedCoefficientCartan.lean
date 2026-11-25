import QuantumMixedWeightSpace
import OccupationTensorCoefficients
import QuantumCreationCartan

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem typeAMixedTensor_Ki_basis (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (p : occupationWeights (Fin (n+1)) l × occupationWeights (Fin (n+1)) m) :
    typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 3)
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p)=
      q^(-(simpleOccupationWeight n p.1.val i-simpleOccupationWeight n p.2.val i)) •
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p) := by
  simp only [Module.Basis.tensorProduct_apply']
  have he : typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 3)
      (quantumOccupationBasis (K:=ℝ) l p.1 ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m p.2)=
      typeAFiniteGenerator q hq hD n l i 3 (quantumOccupationBasis (K:=ℝ) l p.1) ⊗ₜ[ℝ]
      typeAFiniteGenerator q hq hD n m i 2 (quantumOccupationBasis (K:=ℝ) m p.2) := by
    simp [typeAMixedTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductKi,
      typeAOpposite_generator,Module.endTensorEndAlgHom_apply,
      TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator]
  rw [he,typeAFiniteGenerator_Ki_basis,typeAFiniteGenerator_K_basis]
  simp only [← TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul]
  rw [← zpow_add₀ hq]
  congr 1
  ring

theorem occupationTensorCoefficients_mixed_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    occupationTensorCoefficients n l m (typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 2) v)=
      pairLatticeCartan q n i 1 (occupationTensorCoefficients n l m v) := by
  have he : (occupationTensorCoefficients n l m).comp
      (typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 2))=
      (pairLatticeCartan q n i 1).comp (occupationTensorCoefficients n l m) := by
    apply ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).ext
    intro p
    simp only [LinearMap.comp_apply]
    rw [typeAMixedTensor_K_basis]
    simp only [map_smul,Module.Basis.tensorProduct_apply',
      occupationTensorCoefficients_basis,Finsupp.smul_single,smul_eq_mul,mul_one]
    simp [pairLatticeCartan,pairLatticeCartanWeight]
  exact DFunLike.congr_fun he v

theorem occupationTensorCoefficients_mixed_Ki (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    occupationTensorCoefficients n l m (typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 3) v)=
      pairLatticeCartan q n i (-1) (occupationTensorCoefficients n l m v) := by
  have he : (occupationTensorCoefficients n l m).comp
      (typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 3))=
      (pairLatticeCartan q n i (-1)).comp (occupationTensorCoefficients n l m) := by
    apply ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).ext
    intro p
    simp only [LinearMap.comp_apply]
    rw [typeAMixedTensor_Ki_basis]
    simp only [map_smul,Module.Basis.tensorProduct_apply',
      occupationTensorCoefficients_basis,Finsupp.smul_single,smul_eq_mul,mul_one]
    simp [pairLatticeCartan,pairLatticeCartanWeight]
  exact DFunLike.congr_fun he v

end AMSPhysical
