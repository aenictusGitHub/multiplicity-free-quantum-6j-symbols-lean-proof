import QuantumMixedMetric
import TensorTypeACompact

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem typeASymmetric_compact (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) :
    IsCompactTypeAPair q n (occupationCompactBilin q n L)
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L) :=
  ⟨typeACompact_E_adjoint q hq hq1 n L,typeACompact_F_adjoint q hq hq1 n L,
    typeACompact_K_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L,
    typeACompact_Ki_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L⟩

theorem typeAOppositeSymmetric_compact (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) :
    IsCompactTypeAPair q n (occupationOppositeBilin q n L)
      (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L) :=
  ⟨typeAOppositeModule_E_adjoint q hq hq1 n L,typeAOppositeModule_F_adjoint q hq hq1 n L,
    typeAOppositeModule_K_adjoint q hq hq1 n L,typeAOppositeModule_Ki_adjoint q hq hq1 n L⟩

/-- The actual higher-rank mixed tensor representation has the full compact
adjoint structure for its explicit positive product metric. -/
theorem typeAMixedTensor_compact (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m : ℕ) :
    IsCompactTypeAPair (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) m) q n (mixedTensorBilin q n l m)
      (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m) :=
  compactTypeAPair_tensor
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) l) (W:=quantumOccupationSpace ℝ (Fin (n+1)) m)
    (ι:=occupationWeights (Fin (n+1)) l) (κ:=occupationWeights (Fin (n+1)) m) q (ne_of_gt hq) n
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)
    (occupationCompactWeight q n l) (occupationOppositeWeight q n m)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l)
    (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n m)
    (typeASymmetric_compact q hq hq1 n l) (typeAOppositeSymmetric_compact q hq hq1 n m)

theorem mixedTensorBilin_symm (q : ℝ) (n l m : ℕ)
    (v w : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    mixedTensorBilin q n l m v w=mixedTensorBilin q n l m w v  := finiteWeightedPair_symm
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (ι:=occupationWeights (Fin (n+1)) l × occupationWeights (Fin (n+1)) m) _ _ v w

theorem mixedTensorBilin_definite (q : ℝ) (hq : 0<q) (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hv : mixedTensorBilin q n l m v v=0) : v=0 := by
  apply finiteWeightedPair_definite
    (fun xy : occupationWeights (Fin (n+1)) l × occupationWeights (Fin (n+1)) m =>
      occupationCompactWeight q n l xy.1*occupationOppositeWeight q n m xy.2)
    (fun xy => mul_pos (occupationCompactWeight_pos q hq n l xy.1) (occupationOppositeWeight_pos q hq n m xy.2))
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).equivFun.toLinearMap
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).equivFun.injective v
  exact hv

end AMSPhysical
#print axioms AMSPhysical.typeAMixedTensor_compact
