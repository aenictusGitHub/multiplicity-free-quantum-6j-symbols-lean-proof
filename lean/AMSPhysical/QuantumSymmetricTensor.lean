import QuantumMixedCoefficientAction
import QuantumPairCoordinates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeASymmetricTensor (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ) :
    UqTypeA q n →ₐ[ℝ] Module.End ℝ
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  typeATensorRepresentation q hq n (typeAFiniteQuantumRepresentation q hq hD n l)
    (typeAFiniteQuantumRepresentation q hq hD n m)

theorem typeASymmetricTensor_E_tmul (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (v : quantumOccupationSpace ℝ (Fin (n+1)) l)
    (w : quantumOccupationSpace ℝ (Fin (n+1)) m) :
    typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 0) (v ⊗ₜ[ℝ] w)=
      typeAFiniteGenerator q hq hD n l i 0 v ⊗ₜ[ℝ] typeAFiniteGenerator q hq hD n m i 2 w+
        v ⊗ₜ[ℝ] typeAFiniteGenerator q hq hD n m i 0 w := by
  simp [typeASymmetricTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,
    typeACoproductE,Module.endTensorEndAlgHom_apply,
    TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator]

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

def pairSymmetricRaising (q : ℝ) (n : ℕ) (i : Fin n) :
    Module.End ℝ (OccupationPairLattice n →₀ ℝ) :=
  weightedTranslation (latticeRoot i.castSucc i.succ,0)
    (fun p => qInteger q (p.1 i.succ)*q^(simpleOccupationWeight n p.2 i))+
  weightedTranslation (0,latticeRoot i.castSucc i.succ)
    (fun p => qInteger q (p.2 i.succ))

theorem pairSymmetricRaising_single (q : ℝ) (n : ℕ) (i : Fin n) (x y : Fin (n+1) → ℤ) :
    pairSymmetricRaising q n i (Finsupp.single (x,y) 1)=
      Finsupp.single (x+latticeRoot i.castSucc i.succ,y)
        (qInteger q (x i.succ)*q^(simpleOccupationWeight n y i))+
      Finsupp.single (x,y+latticeRoot i.castSucc i.succ) (qInteger q (y i.succ)) := by
  simp [pairSymmetricRaising]

theorem pairSymmetricRaising_coordinate (q : ℝ) (n : ℕ) (i : Fin n)
    (f : OccupationPairLattice n →₀ ℝ) (x y : Fin (n+1) → ℤ) :
    pairSymmetricRaising q n i f (x,y)=
      f (x-latticeRoot i.castSucc i.succ,y)*qInteger q (x i.succ+1)*q^(simpleOccupationWeight n y i)+
      f (x,y-latticeRoot i.castSucc i.succ)*qInteger q (y i.succ+1) := by
  simp only [pairSymmetricRaising,LinearMap.add_apply,Finsupp.add_apply,weightedTranslation_apply]
  have hs : (x,y)-(latticeRoot i.castSucc i.succ,0)=(x-latticeRoot i.castSucc i.succ,y) := by ext <;> simp
  have ht : (x,y)-(0,latticeRoot i.castSucc i.succ)=(x,y-latticeRoot i.castSucc i.succ) := by ext <;> simp
  rw [hs,ht]
  have hj : (x-latticeRoot i.castSucc i.succ) i.succ=x i.succ+1 := by
    rw [Pi.sub_apply,latticeRoot_source _ _ (typeA_root_endpoints n i)]
    ring
  have hi : (y-latticeRoot i.castSucc i.succ) i.succ=y i.succ+1 := by
    rw [Pi.sub_apply,latticeRoot_source _ _ (typeA_root_endpoints n i)]
    ring
  simp only [hj,hi,mul_assoc]

theorem occupationTensorCoefficients_symmetric_E_basis (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    occupationTensorCoefficients n l m
      (typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 0)
        (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m y))=
      pairSymmetricRaising q n i (Finsupp.single (x.val,y.val) 1) := by
  rw [typeASymmetricTensor_E_tmul,map_add,typeAFiniteGenerator_K_basis,TensorProduct.tmul_smul,
    map_smul,occupationTensorCoefficients_E_left,occupationTensorCoefficients_E_right,
    Finsupp.smul_single,pairSymmetricRaising_single]
  simp only [smul_eq_mul]
  congr 1
  congr 1
  ring

theorem occupationTensorCoefficients_symmetric_E (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    occupationTensorCoefficients n l m (typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 0) v)=
      pairSymmetricRaising q n i (occupationTensorCoefficients n l m v) := by
  have hMaps : (occupationTensorCoefficients n l m).comp
      (typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 0))=
      (pairSymmetricRaising q n i).comp (occupationTensorCoefficients n l m) := by
    apply ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).ext
    intro p
    simp only [LinearMap.comp_apply,Module.Basis.tensorProduct_apply']
    rw [occupationTensorCoefficients_symmetric_E_basis,occupationTensorCoefficients_basis]
  exact DFunLike.congr_fun hMaps v

end AMSPhysical
