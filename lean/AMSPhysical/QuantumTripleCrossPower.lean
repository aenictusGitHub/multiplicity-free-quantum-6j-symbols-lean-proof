import QuantumTransferCommutator
import QuantumGeometricPowers
import CrossLadderPowers
import QuantumTripleCupBase

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleFirstContraction_creation_power (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n t : ℕ) (f : OccupationTripleLattice n →₀ ℝ) :
    tripleFirstContraction q n (((tripleRightCreation q n)^(t+1)) f)=
      ((tripleRightCreation q n)^(t+1)) (tripleFirstContraction q n f)+
        qGeometricInteger q ((t+1:ℕ):ℤ) • ((tripleRightCreation q n)^t) (tripleTransfer q n f) := by
  apply quantumCrossLadder_power (tripleFirstContraction q n) (tripleRightCreation q n) (tripleTransfer q n)
    (q^(-2:ℤ)) (fun k =>qGeometricInteger q (k:ℤ)) (qGeometricInteger_zero q)
    (qGeometricInteger_nat_succ q hq hD)
  · intro v
    have h:=DFunLike.congr_fun (tripleFirstContraction_creation_commutator q hq hD n) v
    change tripleFirstContraction q n (tripleRightCreation q n v)-
      tripleRightCreation q n (tripleFirstContraction q n v)=tripleTransfer q n v at h
    exact (sub_eq_iff_eq_add).mp h |>.trans (add_comm _ _)
  · intro v
    exact DFunLike.congr_fun (tripleTransfer_creation_qcommutes q hq n) v

/-- Exact neighboring-pair annihilation on every cup power, including the
middle background required by the AMS rank-two shift. -/
theorem tripleLeftAnnihilation_rightCup_power (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (l h c : ℤ) (t : ℕ) :
    tripleLeftAnnihilation q n (((tripleRightCreation q n)^(t+1)) (tripleCupBase n l h c))=
      (qGeometricInteger q ((t+1:ℕ):ℤ)*((-1:ℝ)^n*q^(-(n:ℤ)-h-c)*qInteger q l)) •
        ((tripleRightCreation q n)^t) (tripleCupBase n (l-1) h (c+1)) := by
  rw [tripleLeftAnnihilation_first_support q n l _
    (tripleRightCreation_pow_first_support q n (Pi.single 0 l) _ (tripleCupBase_first_support n l h c) (t+1))]
  rw [tripleFirstContraction_creation_power q hq hD,tripleCupBase_firstContraction_zero q n hn,
    map_zero,zero_add,tripleCupBase_transfer q n hn,map_smul,smul_smul]

theorem tripleLeftAnnihilation_cupBase_zero (q : ℝ) (n : ℕ) (hn : 0<n) (l h c : ℤ) :
    tripleLeftAnnihilation q n (tripleCupBase n l h c)=0 := by
  rw [tripleLeftAnnihilation_first_support q n l _ (tripleCupBase_first_support n l h c),
    tripleCupBase_firstContraction_zero q n hn]

end AMSPhysical
#print axioms AMSPhysical.tripleLeftAnnihilation_rightCup_power
