import QuantumTransferCoefficients
import FiniteCommutatorSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem tripleFirstContraction_creation_commutator (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) :
    tripleFirstContraction q n*tripleRightCreation q n-
      tripleRightCreation q n*tripleFirstContraction q n=tripleTransfer q n := by
  classical
  unfold tripleRightCreation
  rw [finiteCommutatorSum (tripleFirstContraction q n)
    (fun j : Fin (n+1) =>weightedTranslation (tripleRightCreationShift n j) (tripleRightCreationCoefficient q n j))]
  rw [Finset.sum_eq_single (0:Fin (n+1))]
  · unfold tripleFirstContraction tripleTransfer
    rw [weightedTranslation_commutator]
    have hs : tripleFirstContractionShift n+tripleRightCreationShift n 0=tripleTransferShift n := by
      ext i <;> simp [tripleFirstContractionShift,tripleRightCreationShift,tripleTransferShift,Pi.single_apply] <;> split_ifs <;> ring
    rw [hs]
    congr 1
    funext p
    exact tripleFirstContraction_cross_coefficient q hq hD n p
  · intro j hj hj0
    unfold tripleFirstContraction
    rw [weightedTranslation_commutator]
    have hc : (fun p : OccupationTripleLattice n =>
        tripleRightCreationCoefficient q n j p*tripleFirstContractionCoefficient q n (p+tripleRightCreationShift n j)-
          tripleFirstContractionCoefficient q n p*tripleRightCreationCoefficient q n j (p+tripleFirstContractionShift n))=
        (fun _ =>0) := by
      funext p
      rw [tripleFirstContractionCoefficient_right_shift,tripleRightCoefficient_firstContraction_shift q hq,
        if_neg hj0,zpow_zero,one_mul,add_zero]
      unfold tripleFirstContractionCoefficient
      ring
    rw [hc,weightedTranslation_zero]
  · simp

theorem tripleTransfer_creation_qcommutes (q : ℝ) (hq : q≠0) (n : ℕ) :
    tripleTransfer q n*tripleRightCreation q n=
      q^(-2:ℤ) • (tripleRightCreation q n*tripleTransfer q n) := by
  classical
  unfold tripleRightCreation
  rw [Finset.mul_sum,Finset.sum_mul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply sub_eq_zero.mp
  unfold tripleTransfer
  rw [weightedTranslation_qcommutator]
  have hc : (fun p : OccupationTripleLattice n =>
      tripleRightCreationCoefficient q n j p*tripleTransferCoefficient q n (p+tripleRightCreationShift n j)-
        q^(-2:ℤ)*tripleTransferCoefficient q n p*tripleRightCreationCoefficient q n j (p+tripleTransferShift n))=
      (fun _ =>0) := by
    funext p
    rw [tripleTransferCoefficient_right_shift q hq,tripleRightCoefficient_transfer_shift q hq]
    simp only [zpow_sub₀ hq,zpow_neg]
    ring
  rw [hc,weightedTranslation_zero]

end AMSPhysical
#print axioms AMSPhysical.tripleFirstContraction_creation_commutator
#print axioms AMSPhysical.tripleTransfer_creation_qcommutes
