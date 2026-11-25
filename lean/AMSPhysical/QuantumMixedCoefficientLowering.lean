import QuantumMixedCoefficientAction
import QuantumCreationLowering

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem occupationTensorCoefficients_F_left (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    occupationTensorCoefficients n l m
      (typeAFiniteGenerator q hq hD n l i 1 (quantumOccupationBasis (K:=ℝ) l x) ⊗ₜ[ℝ]
        quantumOccupationBasis (K:=ℝ) m y)=
      Finsupp.single (x.val-latticeRoot i.castSucc i.succ,y.val) (qInteger q (x.val i.castSucc)) := by
  by_cases hp : 0<x.val i.castSucc
  · rw [typeAFiniteGenerator_F_lowered q hq hD n l x i hp,← TensorProduct.smul_tmul',
      map_smul,occupationTensorCoefficients_basis,Finsupp.smul_single]
    simp only [smul_eq_mul,mul_one]
    rw [latticeRoot_swap,sub_eq_add_neg,neg_neg]
    rfl
  · have hz : x.val i.castSucc=0 := by have hh := x.property.1 i.castSucc;omega
    rw [typeAFiniteGenerator_F_zero q hq hD n l x i hz,TensorProduct.zero_tmul,map_zero,hz,qInteger_zero,Finsupp.single_zero]

theorem occupationTensorCoefficients_E_right (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    occupationTensorCoefficients n l m
      (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ]
        typeAFiniteGenerator q hq hD n m i 0 (quantumOccupationBasis (K:=ℝ) m y))=
      Finsupp.single (x.val,y.val+latticeRoot i.castSucc i.succ) (qInteger q (y.val i.succ)) := by
  by_cases hp : 0<y.val i.succ
  · rw [typeAFiniteGenerator_E_raised q hq hD n m y i hp,TensorProduct.tmul_smul,
      map_smul,occupationTensorCoefficients_basis,Finsupp.smul_single]
    simp only [smul_eq_mul,mul_one]
    rfl
  · have hz : y.val i.succ=0 := by have hh := y.property.1 i.succ;omega
    rw [typeAFiniteGenerator_E_zero q hq hD n m y i hz,TensorProduct.tmul_zero,map_zero,hz,qInteger_zero,Finsupp.single_zero]

theorem typeAMixedTensor_F_tmul (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (v : quantumOccupationSpace ℝ (Fin (n+1)) l)
    (w : quantumOccupationSpace ℝ (Fin (n+1)) m) :
    typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 1) (v ⊗ₜ[ℝ] w)=
      typeAFiniteGenerator q hq hD n l i 1 v ⊗ₜ[ℝ] w+
        typeAFiniteGenerator q hq hD n l i 3 v ⊗ₜ[ℝ] typeAFiniteGenerator q hq hD n m i 0 w := by
  simp [typeAMixedTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,
    typeACoproductF,typeAOpposite_generator,Module.endTensorEndAlgHom_apply,
    TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator]

theorem occupationTensorCoefficients_mixed_F_basis (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    occupationTensorCoefficients n l m
      (typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 1)
        (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m y))=
      Finsupp.single (x.val-latticeRoot i.castSucc i.succ,y.val) (qInteger q (x.val i.castSucc))+
      Finsupp.single (x.val,y.val+latticeRoot i.castSucc i.succ)
        (q^(-simpleOccupationWeight n x.val i)*qInteger q (y.val i.succ)) := by
  rw [typeAMixedTensor_F_tmul,map_add,typeAFiniteGenerator_Ki_basis,← TensorProduct.smul_tmul',
    map_smul,occupationTensorCoefficients_F_left,occupationTensorCoefficients_E_right,Finsupp.smul_single]
  rfl

theorem occupationTensorCoefficients_mixed_F (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    occupationTensorCoefficients n l m (typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 1) v)=
      pairLatticeLowering q n i (occupationTensorCoefficients n l m v) := by
  have he : (occupationTensorCoefficients n l m).comp
      (typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 1))=
      (pairLatticeLowering q n i).comp (occupationTensorCoefficients n l m) := by
    apply ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).ext
    intro p
    simp only [LinearMap.comp_apply,Module.Basis.tensorProduct_apply']
    rw [occupationTensorCoefficients_mixed_F_basis,occupationTensorCoefficients_basis]
    simp [pairLatticeLowering,sub_eq_add_neg]
  exact DFunLike.congr_fun he v

end AMSPhysical
