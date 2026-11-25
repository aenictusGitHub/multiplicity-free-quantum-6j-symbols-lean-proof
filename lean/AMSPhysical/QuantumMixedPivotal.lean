import QuantumOppositePivotal
import QuantumMixedCoefficientCartan
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem typeAMixed_inversePivot_basis (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (p : occupationWeights (Fin (n+1)) l × occupationWeights (Fin (n+1)) m) :
    typeAMixedTensor q hq hD n l m (typeAInversePivot q n)
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p)=
      q^(latticePairing (typeAInversePivotalWeight n) p.1.val-latticePairing (typeAInversePivotalWeight n) p.2.val) •
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  have h:=typeAInversePivot_eigen (V:=V) q hq n (typeAMixedTensor q hq hD n l m)
    (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p)
    (fun i => -(simpleOccupationWeight n p.1.val i-simpleOccupationWeight n p.2.val i))
    (fun i =>typeAMixedTensor_Ki_basis q hq hD n l m i p)
  have he : (∑ i : Fin n,(typeAPivotalExponent n i : ℤ)*
      (-(simpleOccupationWeight n p.1.val i-simpleOccupationWeight n p.2.val i)))=
      latticePairing (typeAInversePivotalWeight n) p.1.val-latticePairing (typeAInversePivotalWeight n) p.2.val := by
    rw [← typeAPivotalWeight_pairing,← typeAPivotalWeight_pairing,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    unfold simpleOccupationWeight
    ring
  rw [he] at h
  exact h

theorem typeAMixed_inversePivot_representation (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ) :
    typeAMixedTensor q hq hD n l m (typeAInversePivot q n)=
      TensorProduct.map (finiteOccupationCartan q l (typeAInversePivotalWeight n))
        (finiteOccupationCartan q m (-typeAInversePivotalWeight n)) := by
  apply ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).ext
  intro p
  rw [typeAMixed_inversePivot_basis]
  simp only [Module.Basis.tensorProduct_apply',TensorProduct.map_tmul,finiteOccupationCartan_basis,
    ← TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul,latticePairing_neg_left_typeA]
  rw [← zpow_add₀ hq]
  congr 1
  ring

/-- The ACTUAL full-algebra pivotal trace of the mixed tensor product is
the product of the proved symmetric quantum Weyl dimensions. -/
theorem typeAMixedTensor_pivotal_dimension (q : ℝ) (hq : 0<q) (hD : q-q⁻¹≠0) (n l m : ℕ) :
    LinearMap.trace ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeAMixedTensor q (ne_of_gt hq) hD n l m (typeAInversePivot q n))=
      (qfactorial q (n+l)/(qfactorial q n*qfactorial q l))*
        (qfactorial q (n+m)/(qfactorial q n*qfactorial q m)) := by
  rw [typeAMixed_inversePivot_representation,LinearMap.trace_tensorProduct']
  rw [← typeAInversePivot_representation q (ne_of_gt hq) hD,
    ← typeAOpposite_inversePivot_representation q (ne_of_gt hq) hD,
    typeASymmetric_pivotal_dimension q hq hD,typeAOpposite_pivotal_dimension q hq hD]

end AMSPhysical
#print axioms AMSPhysical.typeAMixedTensor_pivotal_dimension
