import QuantumTripleCupBase
import CoefficientSupportPowers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def tripleOccupationNonnegative (n : ℕ) (p : OccupationTripleLattice n) : Prop :=
  (∀ i,0 ≤ p.1 i) ∧ (∀ i,0 ≤ p.2.1 i) ∧ (∀ i,0 ≤ p.2.2 i)

theorem tripleLeftCreation_nonnegative_support (q : ℝ) (n : ℕ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (tripleOccupationNonnegative n) f) :
    CoefficientSupported (tripleOccupationNonnegative n) (tripleLeftCreation q n f) := by
  unfold tripleLeftCreation
  rw [LinearMap.sum_apply]
  apply coefficientSupported_sum
  intro j
  apply coefficientSupported_weightedTranslation _ _ _ _ f hf
  intro p hp
  constructor
  · intro i
    have hi:=hp.1 i
    simp only [tripleLeftCreationShift,Prod.fst_add,Pi.add_apply,Pi.single_apply]
    split_ifs <;> omega
  · constructor
    · intro i
      have hi:=hp.2.1 i
      simp only [tripleLeftCreationShift,Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.single_apply]
      split_ifs <;> omega
    · intro i
      simpa only [tripleLeftCreationShift,Prod.snd_add,add_zero] using hp.2.2 i

theorem tripleRightCreation_nonnegative_support (q : ℝ) (n : ℕ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (tripleOccupationNonnegative n) f) :
    CoefficientSupported (tripleOccupationNonnegative n) (tripleRightCreation q n f) := by
  unfold tripleRightCreation
  rw [LinearMap.sum_apply]
  apply coefficientSupported_sum
  intro j
  apply coefficientSupported_weightedTranslation _ _ _ _ f hf
  intro p hp
  constructor
  · intro i
    simpa only [tripleRightCreationShift,Prod.fst_add,add_zero] using hp.1 i
  · constructor
    · intro i
      have hi:=hp.2.1 i
      simp only [tripleRightCreationShift,Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.single_apply]
      split_ifs <;> omega
    · intro i
      have hi:=hp.2.2 i
      simp only [tripleRightCreationShift,Prod.snd_add,Pi.add_apply,Pi.single_apply]
      split_ifs <;> omega

theorem tripleCupBase_nonnegative_support (n : ℕ) (l h c : ℤ) (hl : 0 ≤ l) (hh : 0 ≤ h) (hc : 0 ≤ c) :
    CoefficientSupported (tripleOccupationNonnegative n) (tripleCupBase n l h c) := by
  apply coefficientSupported_single
  constructor
  · intro i
    simp only [Pi.single_apply]
    split_ifs <;> omega
  · constructor
    · intro i
      simp only [Pi.single_apply]
      split_ifs <;> omega
    · intro i
      simp only [Pi.single_apply]
      split_ifs <;> omega

end AMSPhysical
