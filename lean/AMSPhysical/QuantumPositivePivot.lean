import QuantumOppositePivotal
import QuantumSymmetricPivotal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeAPositivePivot (q:ℝ) (hq:q≠0) (n:ℕ):UqTypeA q n :=
  typeAChevalley q hq n (typeAInversePivot q n)

theorem typeASymmetric_positivePivot_basis (q:ℝ) (hq:q≠0) (hD:q-q⁻¹≠0) (n L:ℕ)
    (x:occupationWeights (Fin (n+1)) L) :
    typeAFiniteQuantumRepresentation q hq hD n L (typeAPositivePivot q hq n)
      (quantumOccupationBasis (K:=ℝ) L x)=
      q^(latticePairing (-typeAInversePivotalWeight n) x.val) • quantumOccupationBasis (K:=ℝ) L x :=
  typeAOpposite_inversePivot_basis q hq hD n L x

theorem typeASymmetric_positivePivot_dimension (q:ℝ) (hq:0<q) (hD:q-q⁻¹≠0) (n L:ℕ) :
    LinearMap.trace ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L)
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) hD n L (typeAPositivePivot q (ne_of_gt hq) n))=
      qfactorial q (n+L)/(qfactorial q n*qfactorial q L) :=
  typeAOpposite_pivotal_dimension q hq hD n L

theorem typeASymmetricTensor_K_basis_forPositivePivot (q:ℝ) (hq:q≠0) (hD:q-q⁻¹≠0)
    (n l m:ℕ) (i:Fin n) (p:occupationWeights (Fin (n+1)) l × occupationWeights (Fin (n+1)) m) :
    typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 2)
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p)=
      q^(simpleOccupationWeight n p.1.val i+simpleOccupationWeight n p.2.val i) •
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p) := by
  rw [Module.Basis.tensorProduct_apply']
  have he:=typeATensorRepresentation_K q hq n
    (typeAFiniteQuantumRepresentation q hq hD n l) (typeAFiniteQuantumRepresentation q hq hD n m)
    i (quantumOccupationBasis (K:=ℝ) l p.1) (quantumOccupationBasis (K:=ℝ) m p.2)
  change typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 2) _=_ at he
  rw [he]
  change typeAFiniteGenerator q hq hD n l i 2 _ ⊗ₜ[ℝ] typeAFiniteGenerator q hq hD n m i 2 _=_
  rw [typeAFiniteGenerator_K_basis,typeAFiniteGenerator_K_basis]
  simp only [← TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul]
  rw [← zpow_add₀ hq]
  congr 1
  ring

theorem typeASymmetricTensor_positivePivot_basis (q:ℝ) (hq:q≠0) (hD:q-q⁻¹≠0) (n l m:ℕ)
    (p:occupationWeights (Fin (n+1)) l × occupationWeights (Fin (n+1)) m) :
    typeASymmetricTensor q hq hD n l m (typeAPositivePivot q hq n)
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p)=
      q^(latticePairing (-typeAInversePivotalWeight n) p.1.val+
        latticePairing (-typeAInversePivotalWeight n) p.2.val) •
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p) := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  let σ:UqTypeA q n →ₐ[ℝ] Module.End ℝ V:=
    (typeASymmetricTensor q hq hD n l m).comp (typeAChevalley q hq n)
  have he (i:Fin n) :
      σ (typeAAlgebraGenerator q n i 3)
        (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
          (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p)=
      q^(simpleOccupationWeight n p.1.val i+simpleOccupationWeight n p.2.val i) •
        (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
          (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p) := by
    change typeASymmetricTensor q hq hD n l m (typeAChevalley q hq n (typeAAlgebraGenerator q n i 3)) _=_
    rw [typeAChevalley_generator]
    exact typeASymmetricTensor_K_basis_forPositivePivot q hq hD n l m i p
  have hh:=typeAInversePivot_eigen (V:=V) q hq n σ
    (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p)
    (fun i=>simpleOccupationWeight n p.1.val i+simpleOccupationWeight n p.2.val i) he
  have hs:(∑ i:Fin n,(typeAPivotalExponent n i:ℤ)*
      (simpleOccupationWeight n p.1.val i+simpleOccupationWeight n p.2.val i))=
      latticePairing (-typeAInversePivotalWeight n) p.1.val+
        latticePairing (-typeAInversePivotalWeight n) p.2.val := by
    rw [latticePairing_neg_left_typeA,latticePairing_neg_left_typeA,← typeAPivotalWeight_pairing,← typeAPivotalWeight_pairing]
    simp only [← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    unfold simpleOccupationWeight
    ring
  rw [hs] at hh
  exact hh

theorem typeASymmetricTensor_positivePivot_representation (q:ℝ) (hq:q≠0) (hD:q-q⁻¹≠0) (n l m:ℕ) :
    typeASymmetricTensor q hq hD n l m (typeAPositivePivot q hq n)=
      TensorProduct.map (finiteOccupationCartan q l (-typeAInversePivotalWeight n))
        (finiteOccupationCartan q m (-typeAInversePivotalWeight n)) := by
  apply ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).ext
  intro p
  rw [typeASymmetricTensor_positivePivot_basis]
  simp only [Module.Basis.tensorProduct_apply',TensorProduct.map_tmul,finiteOccupationCartan_basis,
    ← TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul]
  rw [← zpow_add₀ hq]
  congr 1
  ring

theorem typeASymmetricTensor_positivePivot_dimension (q:ℝ) (hq:0<q) (hD:q-q⁻¹≠0) (n l m:ℕ) :
    LinearMap.trace ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeASymmetricTensor q (ne_of_gt hq) hD n l m (typeAPositivePivot q (ne_of_gt hq) n))=
      (qfactorial q (n+l)/(qfactorial q n*qfactorial q l))*
        (qfactorial q (n+m)/(qfactorial q n*qfactorial q m)) := by
  rw [typeASymmetricTensor_positivePivot_representation,LinearMap.trace_tensorProduct']
  rw [← typeAOpposite_inversePivot_representation q (ne_of_gt hq) hD,
    ← typeAOpposite_inversePivot_representation q (ne_of_gt hq) hD,
    typeAOpposite_pivotal_dimension q hq hD,typeAOpposite_pivotal_dimension q hq hD]

end AMSPhysical
#print axioms AMSPhysical.typeASymmetricTensor_positivePivot_dimension
