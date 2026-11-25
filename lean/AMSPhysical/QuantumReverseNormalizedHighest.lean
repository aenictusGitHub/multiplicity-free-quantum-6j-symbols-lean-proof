import QuantumReverseFusionHighest
import QuantumMixedNormalization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The parameters a,b label the ACTUAL highest weight a omega_1+b omega_n;
the opposite/symmetric tensor degrees are consequently r+b,r+a. -/
def normalizedReverseMixedHighest (q : ℝ) (n r a b : ℕ) :
    quantumOccupationSpace ℝ (Fin (n+1)) (r+b) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+a) :=
  mixedReflection n (r+b) (r+a) (normalizedMixedHighestVector q n r b a)

theorem normalizedReverseMixedHighest_norm_one (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (r a b : ℕ) :
    reverseMixedTensorBilin q n (r+b) (r+a) (normalizedReverseMixedHighest q n r a b)
      (normalizedReverseMixedHighest q n r a b)=1 := by
  rw [normalizedReverseMixedHighest,mixedReflection_isometry q (ne_of_gt hq)]
  exact normalizedMixedHighestVector_norm_one q hq n b a r hn

theorem normalizedReverseMixedHighest_E_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n r a b : ℕ) (i : Fin n) :
    typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+b) (r+a)
      (typeAAlgebraGenerator q n i 0) (normalizedReverseMixedHighest q n r a b)=0 := by
  have h:=mixedReflection_intertwines q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    n (r+b) (r+a) (typeAAlgebraGenerator q n i.rev 0) (normalizedMixedHighestVector q n r b a)
  rw [typeADynkinReflection_generator,Fin.rev_rev,normalizedMixedHighestVector_E_zero q hq hq1,map_zero] at h
  exact h.symm

theorem normalizedReverseMixedHighest_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n r a b : ℕ) (i : Fin n) :
    typeAReverseMixedTensor q hq hD n (r+b) (r+a) (typeAAlgebraGenerator q n i 2)
      (normalizedReverseMixedHighest q n r a b)=
      q^(mixedHighestDynkin n a b i) • normalizedReverseMixedHighest q n r a b := by
  have h:=mixedReflection_intertwines q hq hD n (r+b) (r+a) (typeAAlgebraGenerator q n i.rev 2)
    (normalizedMixedHighestVector q n r b a)
  rw [typeADynkinReflection_generator,Fin.rev_rev,normalizedMixedHighestVector_K,map_smul,mixedHighestDynkin_rev] at h
  exact h.symm

def normalizedReverseMixedChannel (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) :
    Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) (r+b) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+a)) :=
  algebraCyclicSpan
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) (r+b) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+a))
    (typeAReverseMixedTensor q hq hD n (r+b) (r+a)) (normalizedReverseMixedHighest q n r a b)

end AMSPhysical
