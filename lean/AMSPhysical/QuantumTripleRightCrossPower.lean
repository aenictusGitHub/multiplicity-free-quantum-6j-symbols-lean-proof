import QuantumRightTransferCommutator
import QuantumCommutingTransferPowers
import QuantumTripleThirdSupport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleLastContraction_creation_power (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n t : ℕ) (f : OccupationTripleLattice n →₀ ℝ) :
    tripleLastContraction q n (((tripleLeftCreation q n)^(t+1)) f)=
      (q^(-2:ℤ))^(t+1) • ((tripleLeftCreation q n)^(t+1)) (tripleLastContraction q n f)+
        qGeometricInteger q ((t+1:ℕ):ℤ) • ((tripleLeftCreation q n)^t) (tripleReverseTransfer q n f) := by
  apply qCommutator_commutingTransfer_power (tripleLastContraction q n) (tripleLeftCreation q n)
    (tripleReverseTransfer q n) (q^(-2:ℤ)) (fun k =>qGeometricInteger q (k:ℤ)) (qGeometricInteger_zero q)
    (qGeometricInteger_nat_succ_left q hq hD)
  · intro v
    have h:=DFunLike.congr_fun (tripleLastContraction_creation_qcommutator q hq hD n) v
    change tripleLastContraction q n (tripleLeftCreation q n v)-
      q^(-2:ℤ) • tripleLeftCreation q n (tripleLastContraction q n v)=tripleReverseTransfer q n v at h
    exact (sub_eq_iff_eq_add).mp h |>.trans (add_comm _ _)
  · intro v
    exact DFunLike.congr_fun (tripleReverseTransfer_creation_commutes q hq n) v

theorem tripleRightAnnihilation_leftCup_power (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (l h c : ℤ) (t : ℕ) :
    tripleRightAnnihilation q n (((tripleLeftCreation q n)^(t+1)) (tripleCupBase n l h c))=
      (qGeometricInteger q ((t+1:ℕ):ℤ)*((-1:ℝ)^n*q^(-(n:ℤ)-h-l)*qInteger q c)) •
        ((tripleLeftCreation q n)^t) (tripleCupBase n (l+1) h (c-1)) := by
  rw [tripleRightAnnihilation_third_support q n c _
    (tripleLeftCreation_pow_third_support q n (Pi.single 0 c) _ (tripleCupBase_third_support n l h c) (t+1))]
  rw [tripleLastContraction_creation_power q hq hD,tripleCupBase_lastContraction_zero q n hn,
    map_zero,smul_zero,zero_add,tripleCupBase_reverseTransfer q hq n hn,map_smul,smul_smul]

theorem tripleRightAnnihilation_cupBase_zero (q : ℝ) (n : ℕ) (hn : 0<n) (l h c : ℤ) :
    tripleRightAnnihilation q n (tripleCupBase n l h c)=0 := by
  rw [tripleRightAnnihilation_third_support q n c _ (tripleCupBase_third_support n l h c),
    tripleCupBase_lastContraction_zero q n hn]

end AMSPhysical
#print axioms AMSPhysical.tripleRightAnnihilation_leftCup_power
