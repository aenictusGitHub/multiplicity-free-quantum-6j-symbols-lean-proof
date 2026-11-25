import CompactTrivialHighest
import QuantumMixedNormClosed
import QuantumMixedCompact
import QuantumMixedHighest
import QuantumMixedWeight
import QuantumTypeAPivotal
import QuantumTypeADualEvaluation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Physical coevaluation as an independently constructed actual invariant
tensor, with its normalization fixed by the positive compact metrics. -/
def symmetricCoevaluation (q : ℝ) (n L : ℕ) :
    quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L :=
  mixedHighestVector q n L 0 0

def symmetricPhysicalEvaluation (q : ℝ) (n L : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L) →ₗ[ℝ] ℝ :=
  q^((n*L:ℕ):ℤ) • typeADualEvaluation q n L

theorem symmetricCoevaluation_E (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) (i : Fin n) :
    typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L L
      (typeAAlgebraGenerator q n i 0) (symmetricCoevaluation q n L)=0 :=
  mixedHighestVector_E_zero q hq hq1 n L 0 0 i

theorem symmetricCoevaluation_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) (i : Fin n) :
    typeAMixedTensor q hq hD n L L (typeAAlgebraGenerator q n i 2) (symmetricCoevaluation q n L)=
      symmetricCoevaluation q n L := by
  have h:=mixedHighestVector_K q hq hD n L 0 0 i
  simpa only [mixedHighestDynkin,Nat.cast_zero,zero_mul,add_zero,zpow_zero,one_smul,Nat.add_zero] using h

theorem symmetricCoevaluation_invariant (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) (z : UqTypeA q n) :
    typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L L z
      (symmetricCoevaluation q n L)=typeAQuantumCounit q n z • symmetricCoevaluation q n L := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact compact_weight_zero_highest_invariant (V:=V) q (ne_of_gt hq) n
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L L)
    (mixedTensorBilin q n L L) (typeAMixedTensor_compact q hq hq1 n L L)
    (mixedTensorBilin_definite q hq n L L) (symmetricCoevaluation q n L)
    (symmetricCoevaluation_E q hq hq1 n L)
    (symmetricCoevaluation_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L) z

theorem symmetricCoevaluation_norm_dimension (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (L : ℕ) :
    mixedTensorBilin q n L L (symmetricCoevaluation q n L) (symmetricCoevaluation q n L)=
      qfactorial q (n+L)/(qfactorial q n*qfactorial q L) := by
  unfold symmetricCoevaluation
  have h:=mixedHighestVector_norm_closed q hq n 0 0 L hn
  simp only [Nat.add_zero] at h
  rw [h]
  unfold mixedCouplingNormClosed
  simp only [Nat.cast_zero,zero_mul,neg_zero,zpow_zero,Nat.zero_add,Nat.add_zero,qfactorial_zero,mul_one,one_mul]
  field_simp [qfactorial_ne_zero q hq L,qfactorial_ne_zero q hq n]
  simp

theorem symmetricCoevaluation_norm_actual_pivotal_trace (q : ℝ) (hq : 0<q) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (L : ℕ) :
    mixedTensorBilin q n L L (symmetricCoevaluation q n L) (symmetricCoevaluation q n L)=
      LinearMap.trace ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L)
        (typeAFiniteQuantumRepresentation q (ne_of_gt hq) hD n L (typeAInversePivot q n)) := by
  rw [typeASymmetric_pivotal_dimension q hq hD]
  exact symmetricCoevaluation_norm_dimension q hq n hn L

theorem symmetricPhysicalEvaluation_invariant (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (z : UqTypeA q n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L) :
    symmetricPhysicalEvaluation q n L
      (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L L z v)=
      typeAQuantumCounit q n z*symmetricPhysicalEvaluation q n L v := by
  unfold symmetricPhysicalEvaluation
  simp only [LinearMap.smul_apply,smul_eq_mul]
  have h:=typeADualEvaluation_invariant q hq hq1 n L z v
  change typeADualEvaluation q n L
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L L z v)=
    typeAQuantumCounit q n z*typeADualEvaluation q n L v at h
  rw [h]
  ring

end AMSPhysical
#print axioms AMSPhysical.symmetricCoevaluation_invariant
