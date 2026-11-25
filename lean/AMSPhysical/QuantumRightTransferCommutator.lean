import QuantumRightTransferCoefficients
import FiniteQCommutatorSum
import FiniteCommutatorSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleLastContraction_creation_qcommutator (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) :
    tripleLastContraction q n*tripleLeftCreation q n-
      q^(-2:ℤ) • (tripleLeftCreation q n*tripleLastContraction q n)=tripleReverseTransfer q n := by
  classical
  unfold tripleLeftCreation
  rw [finiteQCommutatorSum (tripleLastContraction q n)
    (fun j : Fin (n+1) =>weightedTranslation (tripleLeftCreationShift n j) (tripleLeftCreationCoefficient q n j))]
  rw [Finset.sum_eq_single (0:Fin (n+1))]
  · unfold tripleLastContraction tripleReverseTransfer
    rw [weightedTranslation_qcommutator]
    have hs : tripleLastContractionShift n+tripleLeftCreationShift n 0=tripleReverseTransferShift n := by
      ext i <;> simp [tripleLastContractionShift,tripleLeftCreationShift,tripleReverseTransferShift,Pi.single_apply] <;> split_ifs <;> ring
    rw [hs]
    congr 1
    funext p
    exact tripleLastContraction_cross_coefficient q hq hD n p
  · intro j hj hj0
    unfold tripleLastContraction
    rw [weightedTranslation_qcommutator]
    have hc : (fun p : OccupationTripleLattice n =>
        tripleLeftCreationCoefficient q n j p*tripleLastContractionCoefficient q n (p+tripleLeftCreationShift n j)-
          q^(-2:ℤ)*tripleLastContractionCoefficient q n p*tripleLeftCreationCoefficient q n j (p+tripleLastContractionShift n))=
        (fun _ =>0) := by
      funext p
      rw [tripleLeftCoefficient_lastContraction_shift q hq]
      simp only [tripleLastContractionCoefficient]
      rw [tripleLastPrefactor_left_shift q hq]
      simp only [
        if_neg hj0,add_zero,tripleLeftCreationShift,Prod.fst_add,Prod.snd_add,Pi.add_apply,
        Pi.single_apply,if_neg (Ne.symm hj0),Pi.zero_apply,add_zero]
      have hQ : q^(-2:ℤ)*q=q^(-1:ℤ) := by
        calc
          _ = q^(-2:ℤ)*q^(1:ℤ) := by rw [zpow_one]
          _ = _ := by rw [← zpow_add₀ hq];norm_num
      linear_combination -(tripleLastContractionPrefactor q n p*tripleLeftCreationCoefficient q n j p*
        qInteger q (p.2.1 0)*qInteger q (p.2.2 0))*hQ
    rw [hc,weightedTranslation_zero]
  · simp

theorem tripleReverseTransfer_creation_commutes (q : ℝ) (hq : q≠0) (n : ℕ) :
    tripleReverseTransfer q n*tripleLeftCreation q n=tripleLeftCreation q n*tripleReverseTransfer q n := by
  classical
  apply sub_eq_zero.mp
  unfold tripleLeftCreation
  rw [finiteCommutatorSum (tripleReverseTransfer q n)
    (fun j : Fin (n+1) =>weightedTranslation (tripleLeftCreationShift n j) (tripleLeftCreationCoefficient q n j))]
  apply Finset.sum_eq_zero
  intro j hj
  unfold tripleReverseTransfer
  rw [weightedTranslation_commutator]
  have hc : (fun p : OccupationTripleLattice n =>
      tripleLeftCreationCoefficient q n j p*tripleReverseTransferCoefficient q n (p+tripleLeftCreationShift n j)-
        tripleReverseTransferCoefficient q n p*tripleLeftCreationCoefficient q n j (p+tripleReverseTransferShift n))=
      (fun _ =>0) := by
    funext p
    rw [tripleReverseTransferCoefficient_left_shift q hq,tripleLeftCoefficient_reverseTransfer_shift q hq]
    ring
  rw [hc,weightedTranslation_zero]

end AMSPhysical
#print axioms AMSPhysical.tripleLastContraction_creation_qcommutator
