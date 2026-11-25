import QuantumSymmetricTensor
import QuantumMixedCompact

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def symmetricTensorBilin (q : ℝ) (n l m : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) →ₗ[ℝ] ℝ :=
  tensorWeightedBilin (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)
    (occupationCompactWeight q n l) (occupationCompactWeight q n m)

theorem symmetricTensorBilin_symm (q : ℝ) (n l m : ℕ)
    (v w : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    symmetricTensorBilin q n l m v w=symmetricTensorBilin q n l m w v :=
  finiteWeightedPair_symm _ _ v w

theorem symmetricTensorBilin_definite (q : ℝ) (hq : 0<q) (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hv : symmetricTensorBilin q n l m v v=0) : v=0 := by
  apply finiteWeightedPair_definite
    (fun xy : occupationWeights (Fin (n+1)) l × occupationWeights (Fin (n+1)) m =>
      occupationCompactWeight q n l xy.1*occupationCompactWeight q n m xy.2)
    (fun xy => mul_pos (occupationCompactWeight_pos q hq n l xy.1) (occupationCompactWeight_pos q hq n m xy.2))
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).equivFun.toLinearMap
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).equivFun.injective v
  exact hv

theorem typeASymmetricTensor_compact (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m : ℕ) :
    IsCompactTypeAPair
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      q n (symmetricTensorBilin q n l m)
      (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m) :=
  compactTypeAPair_tensor
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) l) (W:=quantumOccupationSpace ℝ (Fin (n+1)) m)
    (ι:=occupationWeights (Fin (n+1)) l) (κ:=occupationWeights (Fin (n+1)) m) q (ne_of_gt hq) n
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)
    (occupationCompactWeight q n l) (occupationCompactWeight q n m)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n m)
    (typeASymmetric_compact q hq hq1 n l) (typeASymmetric_compact q hq hq1 n m)

end AMSPhysical
