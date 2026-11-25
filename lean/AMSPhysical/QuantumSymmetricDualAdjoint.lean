import QuantumSymmetricCoevaluation
import QuantumDualSigns
import DiagonalCoevaluation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem symmetricCoevaluation_diagonal (q : ℝ) (n L : ℕ) :
    symmetricCoevaluation q n L=diagonalCoevaluation (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
      (fun x =>occupationDualSign n L x/occupationCompactWeight q n L x) := by
  unfold symmetricCoevaluation mixedHighestVector mixedOccupationTensor diagonalCoevaluation
  apply Finset.sum_congr rfl
  intro x hx
  simp only [mixedHighestCoefficient,occupationDualSign,Nat.cast_zero,zero_mul,neg_zero,zpow_zero,mul_one,
    shiftedOccupation,Pi.single_zero,add_zero]
  rfl

theorem symmetricPhysicalEvaluation_diagonal (q : ℝ) (n L : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L) :
    diagonalEvaluation (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
      (fun x =>occupationDualSign n L x*occupationOppositeWeight q n L x) v=
      symmetricPhysicalEvaluation q n L v := by
  have h : (fun x : occupationWeights (Fin (n+1)) L =>occupationDualSign n L x*occupationOppositeWeight q n L x)=
      (fun x =>q^((n*L:ℕ):ℤ)*occupationDualWeight q n L x) :=
    funext (fun x =>(occupationDualWeight_physical q n L x).symm)
  rw [h,diagonalEvaluation_smul]
  rfl

/-- The independently constructed physical evaluation and coevaluation
are actual compact adjoints, with the full rank-dependent scale proved. -/
theorem symmetricCoevaluation_adjoint (q : ℝ) (hq : 0<q) (n L : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L) :
    mixedTensorBilin q n L L (symmetricCoevaluation q n L) v=symmetricPhysicalEvaluation q n L v := by
  rw [symmetricCoevaluation_diagonal]
  rw [← symmetricPhysicalEvaluation_diagonal]
  apply diagonalCoevaluation_adjoint
  intro x
  rw [div_mul_cancel₀ _ (ne_of_gt (occupationCompactWeight_pos q hq n L x))]

theorem symmetricPhysicalEvaluation_loop_dimension (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (L : ℕ) :
    symmetricPhysicalEvaluation q n L (symmetricCoevaluation q n L)=
      qfactorial q (n+L)/(qfactorial q n*qfactorial q L) := by
  rw [← symmetricCoevaluation_adjoint q hq]
  exact symmetricCoevaluation_norm_dimension q hq n hn L

end AMSPhysical
#print axioms AMSPhysical.symmetricCoevaluation_adjoint
