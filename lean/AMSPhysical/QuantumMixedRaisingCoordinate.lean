import QuantumMixedSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- One exact coefficient of the ACTUAL E action forces the mixed coupling
recurrence. This is independent of the proposed highest-vector coefficients. -/
theorem mixedTensorSum_E_coordinate (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ)
    (i : Fin n) (f : occupationWeights (Fin (n+1)) r → ℝ)
    (t : occupationWeights (Fin (n+1)) r) (hi : 0<t.val i.succ) :
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (r+a)).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (r+b))).repr
      (typeAMixedTensor q hq hD n (r+a) (r+b) (typeAAlgebraGenerator q n i 0) (mixedTensorSum n r a b f))
      (shiftedOccupation n r a 0 (raisedOccupation n r t i hi),shiftedOccupation n r b (Fin.last n) t)=
    f t*qInteger q (t.val i.succ)*q^(-simpleOccupationWeight n t.val i+
      (b:ℤ)*(if i.succ=Fin.last n then 1 else 0))+
      f (raisedOccupation n r t i hi)*qInteger q (t.val i.castSucc+1) := by
  classical
  rw [mixedTensorSum_E_sum,map_add,Finsupp.add_apply]
  congr 1
  · simp only [typeAFiniteGenerator_Ki_basis,TensorProduct.tmul_smul,smul_smul]
    rw [tensor_sum_right_coefficient _ _ (shiftedOccupation n r b (Fin.last n))
      (shiftedOccupation_injective n r b (Fin.last n))]
    rw [shiftedOccupation_high_E q hq hD n r a t i hi,map_smul,Finsupp.smul_apply,
      Module.Basis.repr_self,Finsupp.single_eq_same,smul_eq_mul,mul_one,shiftedOccupation_low_simpleWeight]
    have hpow : -(simpleOccupationWeight n t.val i-(b:ℤ)*(if i.succ=Fin.last n then 1 else 0))=
        -simpleOccupationWeight n t.val i+(b:ℤ)*(if i.succ=Fin.last n then 1 else 0) := by ring
    rw [hpow]
    ring
  · rw [tensor_sum_left_coefficient _ _ (shiftedOccupation n r a 0)
      (shiftedOccupation_injective n r a 0)]
    rw [shiftedOccupation_low_F_raised q hq hD n r b t i hi,map_smul,Finsupp.smul_apply,
      Module.Basis.repr_self,Finsupp.single_eq_same,smul_eq_mul,mul_one]

end AMSPhysical
#print axioms AMSPhysical.mixedTensorSum_E_coordinate
